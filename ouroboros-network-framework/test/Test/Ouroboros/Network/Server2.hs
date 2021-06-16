{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeApplications    #-}

-- just to use 'debugTracer'
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Test.Ouroboros.Network.Server2
  -- ( tests
  -- ) where
  where

import           Control.Exception (AssertionFailed)
import           Control.Monad (replicateM)
import           Control.Monad.Class.MonadAsync
import           Control.Monad.Class.MonadThrow
import           Control.Monad.Class.MonadFork
import           Control.Monad.Class.MonadTest
import           Control.Monad.Class.MonadST    (MonadST)
import           Control.Monad.Class.MonadSTM.Strict
import qualified Control.Monad.Class.MonadSTM as LazySTM
import           Control.Monad.Class.MonadSay
import           Control.Monad.Class.MonadTime
import           Control.Monad.Class.MonadTimer
import           Control.Monad.IOSimPOR
-- import           Control.Monad.IOSim
import           Control.Tracer (Tracer (..), contramap, nullTracer, traceWith)

import           Codec.Serialise.Class (Serialise)
import           Data.ByteString.Lazy (ByteString)
import           Data.Functor (($>), (<&>))
import           Data.List (mapAccumL, intercalate, (\\), isPrefixOf)
import           Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Typeable (Typeable)
import           Data.Void (Void)

import           Text.Printf

import           Test.QuickCheck
import           Test.Tasty.QuickCheck
import           Test.Tasty (TestTree, testGroup)

import qualified Network.Mux as Mux
import qualified Network.Socket as Socket
import           Network.TypedProtocol.Core

import           Network.TypedProtocol.ReqResp.Codec.CBOR
import           Network.TypedProtocol.ReqResp.Client
import           Network.TypedProtocol.ReqResp.Server
import           Network.TypedProtocol.ReqResp.Examples

import           Ouroboros.Network.Channel (fromChannel)
import           Ouroboros.Network.ConnectionId
import           Ouroboros.Network.ConnectionHandler
import           Ouroboros.Network.ConnectionManager.Core
import           Ouroboros.Network.RethrowPolicy
import           Ouroboros.Network.ConnectionManager.Types
import           Ouroboros.Network.IOManager
import           Ouroboros.Network.IOSim
import qualified Ouroboros.Network.InboundGovernor.ControlChannel as Server
import           Ouroboros.Network.Mux
import           Ouroboros.Network.MuxMode
import           Ouroboros.Network.Protocol.Handshake
import           Ouroboros.Network.Protocol.Handshake.Codec ( cborTermVersionDataCodec
                                                            , noTimeLimitsHandshake)
import           Ouroboros.Network.Protocol.Handshake.Unversioned
import           Ouroboros.Network.Protocol.Handshake.Version (Acceptable (..))
import           Ouroboros.Network.Server.RateLimiting (AcceptedConnectionsLimit (..))
import           Ouroboros.Network.Server2 (ServerArguments (..))
import qualified Ouroboros.Network.Server2 as Server
import           Ouroboros.Network.Snocket (Snocket, socketSnocket)
import qualified Ouroboros.Network.Snocket as Snocket
import           Ouroboros.Network.Testing.Utils (genDelayWithPrecision)

import           Test.Ouroboros.Network.Orphans ()  -- ShowProxy ReqResp instance
import           Test.Ouroboros.Network.IOSim (NonFailingBearerInfoScript(..), toBearerInfo)

import Unsafe.Coerce

tests :: TestTree
tests =
  testGroup "Ouroboros.Network.Server2"
  [ testProperty "unidirectional_IO"  prop_unidirectional_IO
  , testProperty "unidirectional_Sim" prop_unidirectional_Sim
  , testProperty "bidirectional_IO"   prop_bidirectional_IO
  , testProperty "bidirectional_Sim"  prop_bidirectional_Sim
  ]

--
-- Server tests
--

-- | The protocol will run three instances of  `ReqResp` protocol; one for each
-- state: warm, hot and established.
--
data ClientAndServerData req resp acc = ClientAndServerData {
    responderAccumulatorFn       :: Fun (acc, req) (acc, resp),
    -- ^ folding function as required by `mapAccumL`, `acc -> req -> (acc, res)`
    -- written using QuickCheck's 'Fun' type; all three responders (hot \/ warm
    -- and established) are using the same
    -- accumulation function, but different initial values.
    accumulatorInit              :: acc,
    -- ^ initial value of accumulator
    hotInitiatorRequests         :: [[req]],
    -- ^ list of requests run by the hot intiator in each round; Running
    -- multiple rounds allows us to test restarting of responders.
    warmInitiatorRequests        :: [[req]],
    -- ^ list of requests run by the warm intiator in each round
    establishedInitiatorRequests :: [[req]]
    -- ^ lsit of requests run by the established intiator in each round
  }
  deriving Show


-- Number of rounds to exhoust all the requests.
--
numberOfRounds :: ClientAndServerData req resp acc ->  Int
numberOfRounds ClientAndServerData {
                  hotInitiatorRequests,
                  warmInitiatorRequests,
                  establishedInitiatorRequests
                } =
    length hotInitiatorRequests
    `max`
    length warmInitiatorRequests
    `max`
    length establishedInitiatorRequests


-- | We use it to generate a list of messages for a list of rounds.  In each
-- round we connect to the same server, and run 'ReqResp' protocol.
--
arbitraryList :: Arbitrary a =>  Gen [[a]]
arbitraryList =
    resize 3 (listOf (resize 3 (listOf (resize 100 arbitrary))))

instance ( Arbitrary req
         , Arbitrary resp
         , Arbitrary acc
         , Function acc
         , CoArbitrary acc
         , Function req
         , CoArbitrary req
         ) => Arbitrary (ClientAndServerData req resp acc) where
    arbitrary =
      ClientAndServerData <$> arbitrary
                          <*> arbitrary
                          <*> arbitraryList
                          <*> arbitraryList
                          <*> arbitraryList

    shrink (ClientAndServerData fun ini hot warm est) = concat
      [ shrink fun  <&> \ fun'  -> ClientAndServerData fun' ini  hot  warm  est
      , shrink ini  <&> \ ini'  -> ClientAndServerData fun  ini' hot  warm  est
      , shrink hot  <&> \ hot'  -> ClientAndServerData fun  ini  hot' warm  est
      , shrink warm <&> \ warm' -> ClientAndServerData fun  ini  hot  warm' est
      , shrink est  <&> \ est'  -> ClientAndServerData fun  ini  hot  warm  est'
      ]

expectedResult :: ClientAndServerData req resp acc
               -> ClientAndServerData req resp acc
               -> [Bundle [resp]]
expectedResult client@ClientAndServerData
                                   { hotInitiatorRequests
                                   , warmInitiatorRequests
                                   , establishedInitiatorRequests
                                   }
               ClientAndServerData { responderAccumulatorFn
                                   , accumulatorInit
                                   } =
    go
      (take rounds $ hotInitiatorRequests         ++ repeat [])
      (take rounds $ warmInitiatorRequests        ++ repeat [])
      (take rounds $ establishedInitiatorRequests ++ repeat [])
  where
    rounds = numberOfRounds client
    go (a : as) (b : bs) (c : cs) =
      Bundle
        (WithHot
          (snd $ mapAccumL
            (applyFun2 responderAccumulatorFn)
            accumulatorInit
            a))
        (WithWarm
          (snd $ mapAccumL
            (applyFun2 responderAccumulatorFn)
            accumulatorInit
            b))
        (WithEstablished
          (snd $ mapAccumL
            (applyFun2 responderAccumulatorFn)
            accumulatorInit
            c))
      : go as bs cs
    go [] [] [] = []
    go _  _  _  = error "expectedResult: impossible happened"


--
-- Various ConnectionManagers
--

type ConnectionManagerMonad m =
       ( MonadAsync m, MonadCatch m, MonadEvaluate m, MonadFork m, MonadMask  m
       , MonadST m, MonadTime m, MonadTimer m, MonadThrow m, MonadThrow (STM m)
       )

type ConnectionState_ muxMode peerAddr m a b =
       ConnectionState peerAddr
                       (Handle muxMode peerAddr ByteString m a b)
                       (HandleError InitiatorResponderMode UnversionedProtocol)
                       (UnversionedProtocol, UnversionedProtocolData)
                       m

-- | Initiator only connection manager.
--
withInitiatorOnlyConnectionManager
    :: forall peerAddr socket acc req resp m a.
       ( ConnectionManagerMonad m

       , Ord peerAddr, Show peerAddr, Typeable peerAddr
       , Serialise req, Serialise resp
       , Typeable req, Typeable resp
       , Eq (LazySTM.TVar m (ConnectionState
                                peerAddr
                                (Handle 'InitiatorMode peerAddr ByteString m [resp] Void)
                                (HandleError 'InitiatorMode UnversionedProtocol)
                                (UnversionedProtocol, UnversionedProtocolData)
                                m))

       -- , Eq (LazySTM.TVar m (ConnectionState_ InitiatorMode peerAddr m [resp] Void))
       -- , Eq (TVar_ (STM m) (ConnectionState_ InitiatorMode peerAddr m [resp] Void))
       -- debugging
       , MonadAsync m
       , MonadLabelledSTM m
       , MonadSay m, Show req, Show resp
       )
    => String
    -- ^ identifier (for logging)
    -> Snocket m socket peerAddr
    -> ClientAndServerData req resp acc
    -- ^ series of request possible to do with the bidirectional connection
    -- manager towards some peer.
    -> (MuxConnectionManager
          InitiatorMode socket peerAddr
          UnversionedProtocol ByteString m [resp] Void
       -> m a)
    -> m a
withInitiatorOnlyConnectionManager
    name snocket
    ClientAndServerData {
        hotInitiatorRequests,
        warmInitiatorRequests,
        establishedInitiatorRequests
      }
    k = do
    mainThreadId <- myThreadId
    -- we pass a `StricTVar` with all the reuqests to each initiator.  This way
    -- the each round (which runs a single instance of `ReqResp` protocol) will
    -- use its own request list.
    hotRequestsVar         <- newTVarIO hotInitiatorRequests
    warmRequestsVar        <- newTVarIO warmInitiatorRequests
    establishedRequestsVar <- newTVarIO establishedInitiatorRequests
    let muxTracer = (name,) `contramap` nullTracer -- mux tracer
    withConnectionManager
      ConnectionManagerArguments {
          -- ConnectionManagerTrace
          cmTracer    = (name,)
                        `contramap` connectionManagerTracer,
          cmTrTracer  = ((name,) . fmap abstractState)
                        `contramap` nullTracer,
         -- MuxTracer
          cmMuxTracer = muxTracer,
          cmIPv4Address = Nothing,
          cmIPv6Address = Nothing,
          cmAddressType = \_ -> Just IPv4Address,
          cmSnocket = snocket,
          connectionDataFlow = const Duplex,
          cmPrunePolicy = simplePrunePolicy,
          cmConnectionsLimits = AcceptedConnectionsLimit {
              acceptedConnectionsHardLimit = maxBound,
              acceptedConnectionsSoftLimit = maxBound,
              acceptedConnectionsDelay     = 0
            },
          cmTimeWaitTimeout = timeWaitTimeout
        }
      (makeConnectionHandler
        muxTracer
        SingInitiatorMode
        clientMiniProtocolBundle
        HandshakeArguments {
            -- TraceSendRecv
            haHandshakeTracer = (name,) `contramap` nullTracer,
            haHandshakeCodec = unversionedHandshakeCodec,
            haVersionDataCodec = cborTermVersionDataCodec unversionedProtocolDataCodec,
            haVersions = unversionedProtocol
              (clientApplication
                hotRequestsVar
                warmRequestsVar
                establishedRequestsVar),
            haAcceptVersion = acceptableVersion,
            haTimeLimits = noTimeLimitsHandshake
          }
        (mainThreadId, debugMuxErrorRethrowPolicy
                    <> debugIOErrorRethrowPolicy
                    <> assertRethrowPolicy))
      (\_ -> HandshakeFailure)
      NotInResponderMode
      k
  where
    clientMiniProtocolBundle :: Mux.MiniProtocolBundle InitiatorMode
    clientMiniProtocolBundle = Mux.MiniProtocolBundle
        [ Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 1,
            Mux.miniProtocolDir = Mux.InitiatorDirectionOnly,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        , Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 2,
            Mux.miniProtocolDir = Mux.InitiatorDirectionOnly,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        , Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 3,
            Mux.miniProtocolDir = Mux.InitiatorDirectionOnly,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        ]

    clientApplication :: StrictTVar m [[req]]
                      -> StrictTVar m [[req]]
                      -> StrictTVar m [[req]]
                      -> Bundle
                          (ConnectionId peerAddr
                            -> ControlMessageSTM m
                            -> [MiniProtocol InitiatorMode ByteString m [resp] Void])
    clientApplication hotRequestsVar
                      warmRequestsVar
                      establishedRequestsVar = Bundle {
        withHot = WithHot $ \_ _ ->
          [ let miniProtocolNum = Mux.MiniProtocolNum 1
            in MiniProtocol {
                miniProtocolNum,
                miniProtocolLimits = Mux.MiniProtocolLimits maxBound,
                miniProtocolRun =
                  reqRespInitiator
                    miniProtocolNum
                    hotRequestsVar
               }
          ],
        withWarm = WithWarm $ \_ _ ->
          [ let miniProtocolNum = Mux.MiniProtocolNum 2
            in MiniProtocol {
                miniProtocolNum,
                miniProtocolLimits = Mux.MiniProtocolLimits maxBound,
                miniProtocolRun =
                  reqRespInitiator
                    miniProtocolNum
                    warmRequestsVar
              }
          ],
        withEstablished = WithEstablished $ \_ _ ->
          [ let miniProtocolNum = Mux.MiniProtocolNum 3
            in MiniProtocol {
                miniProtocolNum,
                miniProtocolLimits = Mux.MiniProtocolLimits maxBound,
                miniProtocolRun =
                  reqRespInitiator
                    miniProtocolNum
                    establishedRequestsVar
              }
          ]
      }

    reqRespInitiator :: Mux.MiniProtocolNum
                     -> StrictTVar m [[req]]
                     -> RunMiniProtocol InitiatorMode ByteString m [resp] Void
    reqRespInitiator protocolNum requestsVar =
      InitiatorProtocolOnly
        (MuxPeer
          ((name,"Initiator",protocolNum,) `contramap` nullTracer) -- TraceSendRecv
          codecReqResp
          (Effect $ do
            reqs <-
              atomically $ do
                requests <- readTVar requestsVar
                case requests of
                  (reqs : rest) -> do
                    writeTVar requestsVar rest $> reqs
                  [] -> pure []
            pure $
              reqRespClientPeer (reqRespClientMap reqs)))


--
-- Constants
--

protocolIdleTimeout :: DiffTime
protocolIdleTimeout = 0.1

timeWaitTimeout :: DiffTime
timeWaitTimeout = 0.1


--
-- Rethrow policies
--

debugMuxErrorRethrowPolicy :: RethrowPolicy
debugMuxErrorRethrowPolicy =
    mkRethrowPolicy $
      \_ MuxError { errorType } ->
        case errorType of
          MuxIOException _ -> ShutdownPeer
          MuxBearerClosed  -> ShutdownPeer
          _                -> ShutdownNode

debugIOErrorRethrowPolicy :: RethrowPolicy
debugIOErrorRethrowPolicy =
    mkRethrowPolicy $
      \_ (_ :: IOError) -> ShutdownNode


assertRethrowPolicy :: RethrowPolicy
assertRethrowPolicy =
    mkRethrowPolicy $
      \_ (_ :: AssertionFailed) -> ShutdownNode


-- | Runs an example server which runs a single 'ReqResp' protocol for any hot
-- \/ warm \/ established peers and also gives access to bidirectional
-- 'ConnectionManager'.  This gives a way to connect to other peers.
-- Slightly unfortunate design decision does not give us a way to create
-- a client per connection.  This means that this connection manager takes list
-- of 'req' type which it will make to the other side (they will be multiplexed
-- across warm \/ how \/ established) protocols.
--
withBidirectionalConnectionManager
    :: forall peerAddr socket acc req resp m a.
       ( ConnectionManagerMonad m

       , Ord peerAddr, Show peerAddr, Typeable peerAddr
       , Serialise req, Serialise resp
       , Typeable req, Typeable resp
       , Eq (LazySTM.TVar m (ConnectionState_ InitiatorResponderMode peerAddr m [resp] acc))

       -- debugging
       , MonadAsync m
       , MonadLabelledSTM m
       , MonadSay m, Show req, Show resp
       )
    => String
    -- ^ identifier (for logging)
    -> Snocket m socket peerAddr
    -> socket
    -- ^ listening socket
    -> Maybe peerAddr
    -> ClientAndServerData req resp acc
    -- ^ series of request possible to do with the bidirectional connection
    -- manager towards some peer.
    -> (MuxConnectionManager
          InitiatorResponderMode socket peerAddr
          UnversionedProtocol ByteString m [resp] acc
       -> peerAddr
       -> Async m Void
       -> m ()
       -> m a)
    -> m a
withBidirectionalConnectionManager name snocket socket localAddress
                                   ClientAndServerData {
                                       responderAccumulatorFn,
                                       accumulatorInit,
                                       hotInitiatorRequests,
                                       warmInitiatorRequests,
                                       establishedInitiatorRequests
                                     }
                                   k = do
    mainThreadId <- myThreadId
    inbgovControlChannel      <- Server.newControlChannel
    -- as in the 'withInitiatorOnlyConnectionManager' we use a `StrictTVar` to
    -- pass list of requests, but since we are also interested in the results we
    -- need to have multable cells to pass the accumulators around.
    hotRequestsVar            <- newTVarIO hotInitiatorRequests
    warmRequestsVar           <- newTVarIO warmInitiatorRequests
    establishedRequestsVar    <- newTVarIO establishedInitiatorRequests
    let resetProtocols = atomically $ do
          writeTVar hotRequestsVar         hotInitiatorRequests
          writeTVar warmRequestsVar        warmInitiatorRequests
          writeTVar establishedRequestsVar establishedInitiatorRequests
    -- we are not using the randomness
    observableStateVar        <- Server.newObservableStateVarFromSeed 0
    let muxTracer = (name,) `contramap` nullTracer -- mux tracer

    withConnectionManager
      ConnectionManagerArguments {
          -- ConnectionManagerTrace
          cmTracer    = (name,)
                        `contramap` connectionManagerTracer,
          cmTrTracer  = ((name,) . fmap abstractState)
                        `contramap` nullTracer,
          -- MuxTracer
          cmMuxTracer    = muxTracer,
          cmIPv4Address  = localAddress,
          cmIPv6Address  = Nothing,
          cmAddressType  = \_ -> Just IPv4Address,
          cmSnocket      = snocket,
          cmTimeWaitTimeout = timeWaitTimeout,
          connectionDataFlow = const Duplex,
          cmPrunePolicy = simplePrunePolicy,
          cmConnectionsLimits = AcceptedConnectionsLimit {
              acceptedConnectionsHardLimit = maxBound,
              acceptedConnectionsSoftLimit = maxBound,
              acceptedConnectionsDelay     = 0
            }
        }
        (makeConnectionHandler
          muxTracer
          SingInitiatorResponderMode
          serverMiniProtocolBundle
          HandshakeArguments {
              -- TraceSendRecv
              haHandshakeTracer = (name,) `contramap` nullTracer,
              haHandshakeCodec = unversionedHandshakeCodec,
              haVersionDataCodec = cborTermVersionDataCodec unversionedProtocolDataCodec,
              haVersions = unversionedProtocol
                            (serverApplication
                              hotRequestsVar
                              warmRequestsVar
                              establishedRequestsVar),
              haAcceptVersion = acceptableVersion,
              haTimeLimits = noTimeLimitsHandshake
            }
          (mainThreadId,   debugMuxErrorRethrowPolicy
                        <> debugIOErrorRethrowPolicy
                        <> assertRethrowPolicy))
          (\_ -> HandshakeFailure)
          (InResponderMode inbgovControlChannel)
      $ \connectionManager ->
          do
            serverAddr <- Snocket.getLocalAddr snocket socket
            withAsync
              (labelMe ("server@" ++ show serverAddr) *>
               Server.run
                ServerArguments {
                    serverSockets = socket :| [],
                    serverSnocket = snocket,
                    serverTracer = (name,) `contramap` nullTracer, -- ServerTrace
                    serverInboundGovernorTracer = (name,) `contramap` nullTracer, -- InboundGovernorTrace
                    serverConnectionLimits = AcceptedConnectionsLimit maxBound maxBound 0,
                    serverConnectionManager = connectionManager,
                    serverProtocolIdleTimeout = protocolIdleTimeout,
                    serverControlChannel = inbgovControlChannel,
                    serverObservableStateVar = observableStateVar
                  }
              )
              (\serverAsync -> k connectionManager serverAddr serverAsync resetProtocols)
          `catch` \(e :: SomeException) -> do
            say (show e)
            throwIO e
  where
    -- for a bidirectional mux we need to define 'Mu.xMiniProtocolInfo' for each
    -- protocol for each direction.
    serverMiniProtocolBundle :: Mux.MiniProtocolBundle InitiatorResponderMode
    serverMiniProtocolBundle = Mux.MiniProtocolBundle
        [ Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 1,
            Mux.miniProtocolDir = Mux.ResponderDirection,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        , Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 1,
            Mux.miniProtocolDir = Mux.InitiatorDirection,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        , Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 2,
            Mux.miniProtocolDir = Mux.ResponderDirection,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        , Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 2,
            Mux.miniProtocolDir = Mux.InitiatorDirection,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        , Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 3,
            Mux.miniProtocolDir = Mux.ResponderDirection,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        , Mux.MiniProtocolInfo {
            Mux.miniProtocolNum = Mux.MiniProtocolNum 3,
            Mux.miniProtocolDir = Mux.InitiatorDirection,
            Mux.miniProtocolLimits = Mux.MiniProtocolLimits maxBound
          }
        ]

    serverApplication :: StrictTVar m [[req]]
                      -> StrictTVar m [[req]]
                      -> StrictTVar m [[req]]
                      -> Bundle
                          (ConnectionId peerAddr
                      -> ControlMessageSTM m
                      -> [MiniProtocol InitiatorResponderMode ByteString m [resp] acc])
    serverApplication hotRequestsVar
                      warmRequestsVar
                      establishedRequestsVar
                      = Bundle {
        withHot = WithHot $ \_ _ ->
          [ let miniProtocolNum = Mux.MiniProtocolNum 1
            in MiniProtocol {
                miniProtocolNum,
                miniProtocolLimits = Mux.MiniProtocolLimits maxBound,
                miniProtocolRun =
                  reqRespInitiatorAndResponder
                    miniProtocolNum
                    responderAccumulatorFn
                    accumulatorInit
                    hotRequestsVar
               }
          ],
        withWarm = WithWarm $ \_ _ ->
          [ let miniProtocolNum = Mux.MiniProtocolNum 2
            in MiniProtocol {
                miniProtocolNum,
                miniProtocolLimits = Mux.MiniProtocolLimits maxBound,
                miniProtocolRun =
                  reqRespInitiatorAndResponder
                    miniProtocolNum
                    responderAccumulatorFn
                    accumulatorInit
                    warmRequestsVar
              }
          ],
        withEstablished = WithEstablished $ \_ _ ->
          [ let miniProtocolNum = Mux.MiniProtocolNum 3
            in MiniProtocol {
                miniProtocolNum,
                miniProtocolLimits = Mux.MiniProtocolLimits maxBound,
                miniProtocolRun =
                  reqRespInitiatorAndResponder
                    (Mux.MiniProtocolNum 3)
                    responderAccumulatorFn
                    accumulatorInit
                    establishedRequestsVar
              }
          ]
      }

    reqRespInitiatorAndResponder
      :: Mux.MiniProtocolNum
      -> Fun (acc, req) (acc, resp)
      -> acc
      -> StrictTVar m [[req]]
      -> RunMiniProtocol InitiatorResponderMode ByteString m [resp] acc
    reqRespInitiatorAndResponder protocolNum fn accInit requestsVar =
      InitiatorAndResponderProtocol
        (MuxPeer
          ((name,"Initiator",protocolNum,) `contramap` nullTracer) -- TraceSendRecv
          codecReqResp
          (Effect $ do
            reqs <-
              atomically $ do
                requests <- readTVar requestsVar
                case requests of
                  (reqs : rest) -> do
                    writeTVar requestsVar rest $> reqs
                  [] -> pure []
            pure $
              reqRespClientPeer
              (reqRespClientMap reqs)))
        (MuxPeer
          ((name,"Responder",protocolNum,) `contramap` nullTracer) -- TraceSendRecv
          codecReqResp
          (reqRespServerPeer $ reqRespServerMapAccumL' (applyFun2 fn) accInit))

    reqRespServerMapAccumL' :: (acc -> req -> (acc, resp))
                            -> acc
                            -> ReqRespServer req resp m acc
    reqRespServerMapAccumL' fn = go
      where
        go acc =
          ReqRespServer {
              recvMsgReq = \req ->
                  let (acc', resp) = fn acc req
                  in return (resp, go acc'),
              recvMsgDone = return acc
            }




-- | Run all initiator mini-protocols and collect results. Throw exception if
-- any of the thread returned an exception.
--
-- This function assumes that there's one established, one warm and one hot
-- mini-protocol, which is compatible with both
--
-- * 'withInitiatorOnlyConnectionManager', and
-- * 'withBidirectionalConnectionManager'.
--
runInitiatorProtocols
    :: forall muxMode m a b.
       ( MonadAsync      m
       , MonadCatch      m
       , MonadSTM        m
       , MonadThrow (STM m)
       , HasInitiator muxMode ~ True
       , MonadSay        m
       )
    => SingMuxMode muxMode
    -> Mux.Mux muxMode m
    -> MuxBundle muxMode ByteString m a b
    -> m (Bundle a)
runInitiatorProtocols
    singMuxMode mux
    (Bundle (WithHot  [hotPtcl])
            (WithWarm [warmPtcl])
            (WithEstablished [establishedPtcl])) = do
      -- start all protocols
      hotSTM <- runInitiator hotPtcl
      warmSTM <- runInitiator warmPtcl
      establishedSTM <- runInitiator establishedPtcl

      -- await for their termination
      hotRes <- atomically hotSTM
      warmRes <- atomically warmSTM
      establishedRes <- atomically establishedSTM
      case (hotRes, warmRes, establishedRes) of
        (Left err, _, _) -> throwIO err
        (_, Left err, _) -> throwIO err
        (_, _, Left err) -> throwIO err
        (Right hot, Right warm, Right established) ->
          pure $ Bundle (WithHot hot) (WithWarm warm) (WithEstablished established)
  where
    runInitiator :: MiniProtocol muxMode ByteString m a b
                 -> m (STM m (Either SomeException a))
    runInitiator ptcl =
      Mux.runMiniProtocol
        mux
        (miniProtocolNum ptcl)
        (case singMuxMode of
          SingInitiatorMode -> Mux.InitiatorDirectionOnly
          SingInitiatorResponderMode -> Mux.InitiatorDirection)
        Mux.StartEagerly
        (runMuxPeer
          (case miniProtocolRun ptcl of
            InitiatorProtocolOnly initiator -> initiator
            InitiatorAndResponderProtocol initiator _ -> initiator)
          . fromChannel)

runInitiatorProtocols _singMuxMode _mux (Bundle {}) =
    error "runInitiatorProtocols: unsupported"


--
-- Experiments \/ Demos & Properties
--


-- | This test runs an intiator only connection manager (client side) and bidrectional
-- connection manager (which runs a server).   The the client connect to the
-- server and runs protocols to completion.
--
-- There is a good reason why we don't run two bidrectional connection managers;
-- If we would do that, when the either side terminates the connection the
-- client side server would through an exception as it is listening.
--
unidirectionalExperiment
    :: forall peerAddr socket acc req resp m.
       ( ConnectionManagerMonad m
       , MonadAsync m
       , MonadLabelledSTM m
       , MonadSay m

       , Ord peerAddr, Show peerAddr, Typeable peerAddr, Eq peerAddr
       , Eq (LazySTM.TVar m (ConnectionState
                                peerAddr
                                (Handle 'InitiatorMode peerAddr ByteString m [resp] Void)
                                (HandleError 'InitiatorMode UnversionedProtocol)
                                (UnversionedProtocol, UnversionedProtocolData)
                                m))
       -- , Eq (LazySTM.TVar m (ConnectionState_ InitiatorMode          peerAddr m [resp] Void))
       , Eq (LazySTM.TVar m (ConnectionState_ InitiatorResponderMode peerAddr m [resp] acc))
       , Serialise req, Show req
       , Serialise resp, Show resp, Eq resp
       , Typeable req, Typeable resp
       )
    => Snocket m socket peerAddr
    -> socket
    -> ClientAndServerData req resp acc
    -> m Property
unidirectionalExperiment snocket socket clientAndServerData = do
    withInitiatorOnlyConnectionManager
      "client" snocket clientAndServerData
      $ \connectionManager ->
        withBidirectionalConnectionManager
          "server" snocket socket Nothing clientAndServerData
          $ \_ serverAddr serverAsync _ -> do
            link serverAsync
            -- client → server: connect
            (rs :: [Either SomeException (Bundle [resp])]) <-
                replicateM
                  (numberOfRounds clientAndServerData)
                  (bracket
                     (requestOutboundConnection connectionManager serverAddr)
                     (\_ -> unregisterOutboundConnection connectionManager serverAddr)
                     (\connHandle -> do
                      case connHandle of
                        Connected _ _ (Handle mux muxBundle _
                                        :: Handle InitiatorMode peerAddr ByteString m [resp] Void) ->
                          try @_ @SomeException $
                            (runInitiatorProtocols
                              SingInitiatorMode mux muxBundle
                              :: m (Bundle [resp])
                            )
                        Disconnected _ err ->
                          throwIO (userError $ "unidirectionalExperiment: " ++ show err))
                  )
            pure $
              foldr
                (\ (r, expected) acc ->
                  case r of
                    Left err -> counterexample (show err) False
                    Right a -> a === expected .&&. acc)
                (property True)
                $ zip rs (expectedResult clientAndServerData clientAndServerData)

prop_unidirectional_Sim :: ClientAndServerData Int Int Int -> Property
prop_unidirectional_Sim clientAndServerData =
  simulatedPropertyWithTimeout 7200 $ do
    net   <- newNetworkState (singletonScript noAttenuation) 10
    let snock = mkSnocket net debugTracer
    fd <- Snocket.open snock Snocket.TestFamily
    Snocket.bind   snock fd serverAddr
    Snocket.listen snock fd
    unidirectionalExperiment snock fd clientAndServerData
  where
    serverAddr = Snocket.TestAddress (0 :: Int)

prop_unidirectional_IO
  :: ClientAndServerData Int Int Int
  -> Property
prop_unidirectional_IO clientAndServerData =
    ioProperty $ do
      withIOManager $ \iomgr ->
        bracket
          (Socket.socket Socket.AF_INET Socket.Stream Socket.defaultProtocol)
          Socket.close
          $ \socket -> do
              associateWithIOManager iomgr (Right socket)
              addr <- head <$> Socket.getAddrInfo Nothing (Just "127.0.0.1") (Just "0")
              Socket.bind socket (Socket.addrAddress addr)
              Socket.listen socket maxBound
              unidirectionalExperiment
                (socketSnocket iomgr)
                socket
                clientAndServerData


-- | Bidirectional send and receive.
--
bidirectionalExperiment
    :: forall peerAddr socket acc req resp m.
       ( ConnectionManagerMonad m
       , MonadAsync m
       , MonadLabelledSTM m
       , MonadSay m

       , Ord peerAddr, Show peerAddr, Typeable peerAddr, Eq peerAddr
       , Eq (LazySTM.TVar m (ConnectionState_ 'InitiatorResponderMode peerAddr m [resp] acc))

       , Serialise req, Show req
       , Serialise resp, Show resp, Eq resp
       , Typeable req, Typeable resp
       , Show acc
       )
    => Snocket m socket peerAddr
    -> socket
    -> socket
    -> peerAddr
    -> peerAddr
    -> ClientAndServerData req resp acc
    -> ClientAndServerData req resp acc
    -> m Property
bidirectionalExperiment
    snocket socket0 socket1 localAddr0 localAddr1
    clientAndServerData0 clientAndServerData1 = do
      lock <- newTMVarIO ()
      let withLock _ = id
      -- connect lock: only one side can run 'requestOutboundConnection' in
      -- turn.  Otherwise when both sides call 'requestOutboundConnection' they
      -- both will run 'connect' and one of the calls will fail.  Using a lock
      -- forces to block until negotiation is done, which is not ideal.
      withBidirectionalConnectionManager
        "node-0" snocket socket0 (Just localAddr0) clientAndServerData0
        (\connectionManager0 _serverAddr0 serverAsync0 _ ->
          withBidirectionalConnectionManager
            "node-1" snocket socket1 (Just localAddr1) clientAndServerData1
            (\connectionManager1 _serverAddr1 serverAsync1 _ -> do
              link serverAsync0
              link serverAsync1
              threadDelay 2
              -- runInitiatorProtocols returns a list of results per each
              -- protocol in each bucket (warm \/ hot \/ established); but
              -- we run only one mini-protocol. We can use `concat` to
              -- flatten the results.
              ( rs0 :: [Either SomeException (Bundle [resp])]
                , rs1 :: [Either SomeException (Bundle [resp])]
                ) <-
                -- Run initiator twice; this tests if the responders on
                -- the other end are restarted.
                (replicateM
                  (numberOfRounds clientAndServerData0)
                  (bracket
                    (withLock lock
                      (requestOutboundConnection
                        connectionManager0
                        localAddr1))
                    (\_ ->
                      unregisterOutboundConnection
                        connectionManager0
                        localAddr1)
                    (\connHandle ->
                      case connHandle of
                        Connected _ _ (Handle mux muxBundle _) -> do
                          try @_ @SomeException $
                            runInitiatorProtocols
                              SingInitiatorResponderMode
                              mux muxBundle
                        Disconnected _ err ->
                          throwIO (userError $ "bidirectionalExperiment: " ++ show err)
                  )))
                `concurrently`
                (replicateM
                  (numberOfRounds clientAndServerData1)
                  (bracket
                    (withLock lock
                      (requestOutboundConnection
                        connectionManager1
                        localAddr0))
                    (\_ ->
                      unregisterOutboundConnection
                        connectionManager1
                        localAddr0)
                    (\connHandle ->
                      case connHandle of
                        Connected _ _ (Handle mux muxBundle _) -> do
                          try @_ @SomeException $
                            runInitiatorProtocols
                              SingInitiatorResponderMode
                              mux muxBundle
                        Disconnected _ err ->
                          throwIO (userError $ "bidirectionalExperiment: " ++ show err)
                  )))

              pure $
                foldr
                  (\ (r, expected) acc ->
                    case r of
                      Left err -> counterexample (show err) False
                      Right a -> a === expected .&&. acc)
                  (property True)
                  (zip rs0 (expectedResult clientAndServerData0 clientAndServerData1))
                .&&.
                foldr
                  (\ (r, expected) acc ->
                    case r of
                      Left err -> counterexample (show err) False
                      Right a -> a === expected .&&. acc)
                  (property True)
                  (zip rs1 (expectedResult clientAndServerData1 clientAndServerData0))
                ))


prop_bidirectional_Sim :: NonFailingBearerInfoScript -> ClientAndServerData Int Int Int -> ClientAndServerData Int Int Int -> Property
prop_bidirectional_Sim (NonFailingBearerInfoScript script) data0 data1 =
  simulatedPropertyWithTimeout 7200 $ do
    net <- newNetworkState (singletonScript noAttenuation) 10 -- script' 10
    let snock = mkSnocket net debugTracer
    bracket ((,) <$> Snocket.open snock Snocket.TestFamily
                 <*> Snocket.open snock Snocket.TestFamily)
            (\ (socket0, socket1) -> Snocket.close snock socket0 >>
                                     Snocket.close snock socket1)
      $ \ (socket0, socket1) -> do
        let addr0 = Snocket.TestAddress (0 :: Int)
            addr1 = Snocket.TestAddress 1
        Snocket.bind   snock socket0 addr0
        Snocket.bind   snock socket1 addr1
        Snocket.listen snock socket0
        Snocket.listen snock socket1
        bidirectionalExperiment snock socket0 socket1 addr0 addr1 data0 data1
  -- where
  --   script' = toBearerInfo <$> script

prop_bidirectional_IO
    :: ClientAndServerData Int Int Int
    -> ClientAndServerData Int Int Int
    -> Property
prop_bidirectional_IO data0 data1 =
    ioProperty $ do
      withIOManager $ \iomgr ->
        bracket
          ((,)
            <$> Socket.socket Socket.AF_INET Socket.Stream Socket.defaultProtocol
            <*> Socket.socket Socket.AF_INET Socket.Stream Socket.defaultProtocol)
          (\(socket0,socket1) -> Socket.close socket0
                              >> Socket.close socket1)
          $ \(socket0, socket1) -> do
            associateWithIOManager iomgr (Right socket0)
            associateWithIOManager iomgr (Right socket1)
            Socket.setSocketOption socket0 Socket.ReuseAddr 1
            Socket.setSocketOption socket1 Socket.ReuseAddr 1
#if !defined(mingw32_HOST_OS)
            Socket.setSocketOption socket0 Socket.ReusePort 1
            Socket.setSocketOption socket1 Socket.ReusePort 1
#endif
            -- TODO: use ephemeral ports
            let hints = Socket.defaultHints { Socket.addrFlags = [Socket.AI_ADDRCONFIG, Socket.AI_PASSIVE] }
            addr0 : _ <- Socket.getAddrInfo (Just hints) (Just "127.0.0.1") (Just "0")
            addr1 : _ <- Socket.getAddrInfo (Just hints) (Just "127.0.0.1") (Just "0")
            Socket.bind socket0 (Socket.addrAddress addr0)
            Socket.bind socket1 (Socket.addrAddress addr1)
            addr0' <- Socket.getSocketName socket0
            addr1' <- Socket.getSocketName socket1
            Socket.listen socket0 10
            Socket.listen socket1 10

            bidirectionalExperiment
              (socketSnocket iomgr)
              socket0
              socket1
              addr0'
              addr1'
              data0
              data1

data ConnectionEvent req resp acc peerAddr
  = StartClient DiffTime peerAddr (ClientAndServerData req resp acc)
  | StartServer DiffTime peerAddr (ClientAndServerData req resp acc)
  | ClientConnection   DiffTime peerAddr
  | InboundNodeToNode  DiffTime peerAddr
  | OutboundNodeToNode DiffTime peerAddr
  deriving (Show, Functor)

newtype MultiNodeScript req resp acc peerAddr = MultiNodeScript [ConnectionEvent req resp acc peerAddr]
  deriving (Show, Functor)

data ScriptState peerAddr = ScriptState { startedClients      :: [peerAddr]
                                        , startedServers      :: [peerAddr]
                                        , clientConnections   :: [peerAddr]
                                        , inboundConnections  :: [peerAddr]
                                        , outboundConnections :: [peerAddr] }

instance (Arbitrary peerAddr, Arbitrary req, Arbitrary resp, Arbitrary acc,
          Function acc, CoArbitrary acc,
          Function req, CoArbitrary req, Eq peerAddr) =>
         Arbitrary (MultiNodeScript req resp acc peerAddr) where
  arbitrary = do
      NonNegative len <- scale (`div` 2) arbitrary
      MultiNodeScript <$> go (ScriptState [] [] [] [] []) (len :: Integer)
    where
      delay = genDelayWithPrecision 2
      go _ 0 = pure []
      go s@ScriptState{..} n = do
        event <- frequency $
                    [ (1, StartClient        <$> delay <*> newClient <*> arbitrary)
                    , (1, StartServer        <$> delay <*> newServer <*> arbitrary) ] ++
                    [ (4, ClientConnection   <$> delay <*> elements possibleClientConnections)   | not $ null possibleClientConnections] ++
                    [ (4, InboundNodeToNode  <$> delay <*> elements possibleInboundConnections)  | not $ null possibleInboundConnections] ++
                    [ (4, OutboundNodeToNode <$> delay <*> elements possibleOutboundConnections) | not $ null possibleOutboundConnections]
        let next (StartClient        _ a _) = s{ startedClients      = a : startedClients }
            next (StartServer        _ a _) = s{ startedServers      = a : startedServers }
            next (ClientConnection   _ a)   = s{ clientConnections   = a : clientConnections }
            next (InboundNodeToNode  _ a)   = s{ inboundConnections  = a : inboundConnections }
            next (OutboundNodeToNode _ a)   = s{ outboundConnections = a : outboundConnections }
        (event :) <$> go (next event) (n - 1)
        where
          possibleClientConnections   = startedClients \\ clientConnections
          possibleInboundConnections  = startedServers \\ inboundConnections
          possibleOutboundConnections = startedServers \\ outboundConnections
          newClient = arbitrary `suchThat` (`notElem` startedClients)
          newServer = arbitrary `suchThat` (`notElem` startedServers)

  shrink (MultiNodeScript events) = MultiNodeScript . makeValid <$> shrinkList shrinkEvent events
    where
      makeValid = go (ScriptState [] [] [] [] [])
        where
          go s [] = []
          go s (e : es)
            | pre e s   = e : go (next e s) es
            | otherwise = go s es

      pre e ScriptState{..} =
        case e of
          StartClient        _ a _ -> notElem a startedClients
          StartServer        _ a _ -> notElem a startedServers
          ClientConnection   _ a   -> elem a startedClients && notElem a clientConnections
          InboundNodeToNode  _ a   -> elem a startedServers && notElem a inboundConnections
          OutboundNodeToNode _ a   -> elem a startedServers -- && notElem a outboundConnections

      next e s@ScriptState{..} =
        case e of
          StartClient        _ a _ -> s{ startedClients      = a : startedClients }
          StartServer        _ a _ -> s{ startedServers      = a : startedServers }
          ClientConnection   _ a   -> s{ clientConnections   = a : clientConnections }
          InboundNodeToNode  _ a   -> s{ inboundConnections  = a : inboundConnections }
          OutboundNodeToNode _ a   -> s{ outboundConnections = a : outboundConnections }

      shrinkTime t | t > 0 = [0]
      shrinkTime _         = []

      shrinkEvent (StartServer t a p) =
        (StartServer t a <$> shrink p) ++
        (shrinkTime t <&> \ t' -> StartServer t' a p)
      shrinkEvent (StartClient t a p) = StartClient t a <$> shrink p
      shrinkEvent (InboundNodeToNode t a)  = shrinkTime t <&> \ t' -> InboundNodeToNode t' a
      shrinkEvent (OutboundNodeToNode t a) = shrinkTime t <&> \ t' -> OutboundNodeToNode t' a
      shrinkEvent _ = []

newtype TestAddr = TestAddr { unTestAddr :: Snocket.TestAddress Int }
  deriving (Show, Eq, Ord)

ppAddr :: Show a => Snocket.TestAddress a -> String
ppAddr (Snocket.TestAddress x) = "ip:" ++ show x

instance Arbitrary TestAddr where
  arbitrary = TestAddr . Snocket.TestAddress <$> choose (1, 100)

-- | Run a central server that talks to any number of clients and other nodes.
multinodeExperiment
    :: forall peerAddr socket acc req resp m.
       ( ConnectionManagerMonad m
       , MonadAsync m
       , MonadLabelledSTM m
       , MonadSay m
       , peerAddr ~ Snocket.TestAddress Int
       , Ord peerAddr, Show peerAddr, Typeable peerAddr, Eq peerAddr
       , Eq (LazySTM.TVar m (ConnectionState
                                peerAddr
                                (Handle 'InitiatorMode peerAddr ByteString m [resp] Void)
                                (HandleError 'InitiatorMode UnversionedProtocol)
                                (UnversionedProtocol, UnversionedProtocolData)
                                m))
       -- , Eq (LazySTM.TVar m (ConnectionState_ InitiatorMode          peerAddr m [resp] Void))
       , Eq (LazySTM.TVar m (ConnectionState_ InitiatorResponderMode peerAddr m [resp] acc))
       , Serialise req, Show req
       , Serialise resp, Show resp, Eq resp
       , Typeable req, Typeable resp
       )
    => Snocket m socket peerAddr
    -> Snocket.AddressFamily peerAddr
    -> peerAddr
    -> ClientAndServerData req resp acc
    -> MultiNodeScript req resp acc peerAddr
    -> m Property
multinodeExperiment snocket addrFamily serverAddr serverData (MultiNodeScript script) = do
  -- Start the main server
  socket <- Snocket.open snocket addrFamily
  Snocket.bind   snocket socket serverAddr
  Snocket.listen snocket socket
  lock <- newTMVarIO ()
  withBidirectionalConnectionManager "main" snocket socket (Just serverAddr) serverData
    $ \ connectionManager _ serverAsync resetServerProtocols -> do
        link serverAsync
        loop lock connectionManager resetServerProtocols Map.empty Map.empty [] script
  where
    loop _ _ _ _ _ results [] = foldr (.&&.) (property True) <$> atomically (mapM readTMVar results)
    loop lock serverCM resetServerProtocols nodes clients results (event : script) =
      case event of

        StartClient delay localAddr clientData -> do
          threadDelay delay
          withInitiatorOnlyConnectionManager ("client-" ++ show localAddr) snocket clientData
            $ \ connectionManager ->
              loop lock serverCM resetServerProtocols nodes (Map.insert localAddr (connectionManager, clientData) clients) results script

        StartServer delay localAddr serverData -> do
          threadDelay delay
          fd <- Snocket.open snocket addrFamily
          Snocket.bind   snocket fd localAddr
          Snocket.listen snocket fd
          withBidirectionalConnectionManager ("node-" ++ show localAddr) snocket fd (Just localAddr) serverData
            $ \ connectionManager _ serverAsync _ -> do
              link serverAsync
              loop lock serverCM resetServerProtocols (Map.insert localAddr (connectionManager, serverData) nodes) clients results script

        ClientConnection delay clientAddr -> do
          threadDelay delay
          let (cm, clientData) = clients Map.! clientAddr
          result <- runConnection lock SingInitiatorMode cm clientAddr serverAddr serverData clientData
          loop lock serverCM resetServerProtocols nodes clients (result : results) script

        InboundNodeToNode delay nodeAddr -> do
          threadDelay delay
          let (cm, nodeData) = nodes Map.! nodeAddr
          result <- runConnection lock SingInitiatorResponderMode cm nodeAddr serverAddr serverData nodeData
          loop lock serverCM resetServerProtocols nodes clients (result : results) script

        OutboundNodeToNode delay nodeAddr -> do
          threadDelay delay
          let (_, nodeData) = nodes Map.! nodeAddr
          result <- runConnection lock SingInitiatorResponderMode serverCM serverAddr nodeAddr nodeData serverData
          resetServerProtocols
          loop lock serverCM resetServerProtocols nodes clients (result : results) script

    runConnection :: forall muxMode handleError a.
      (HasInitiator muxMode ~ True, Show handleError)
      => StrictTMVar m ()
      -> SingMuxMode muxMode
      -> ConnectionManager muxMode socket peerAddr
                           (Handle muxMode peerAddr ByteString m [resp] a)
                           handleError m
     -> peerAddr -> peerAddr
     -> ClientAndServerData req resp acc
     -> ClientAndServerData req resp acc
     -> m (StrictTMVar m Property)
    runConnection lock singMuxMode connectionManager clientAddr serverAddr serverData clientData = do
      result <- atomically newEmptyTMVar
      labelTMVarIO result ("res(" ++ ppAddr clientAddr ++ "=>" ++ ppAddr serverAddr ++ ")")
      now <- getCurrentTime
      forkIO $ do
        labelMe (ppAddr clientAddr ++ "=>" ++ ppAddr serverAddr)
        (rs :: [Either SomeException (Bundle [resp])]) <-
            replicateM
              (numberOfRounds clientData)
              (bracket
                 (withLock lock
                  (requestOutboundConnection connectionManager serverAddr))
                 (\_ -> unregisterOutboundConnection connectionManager serverAddr)
                 (\connHandle -> do
                  say "Got connection"
                  case connHandle of
                    Connected _ _ (Handle mux muxBundle _ :: Handle muxMode peerAddr ByteString m [resp] a) ->
                      try @_ @SomeException $ runInitiatorProtocols singMuxMode mux muxBundle
                    Disconnected _ err ->
                      throwIO (userError $ "unidirectionalExperiment: " ++ show err))
              )
        atomically $ putTMVar result $ counterexample ("Connection at " ++ show now) $
          foldr
            (\ (r, expected) acc ->
              case r of
                Left err -> counterexample (show err) False
                Right a -> a === expected .&&. acc)
            (property True)
            $ zip rs (expectedResult clientData serverData)
      return result

labelMe :: MonadFork m => String -> m ()
labelMe s = myThreadId >>= (`labelThread` s)

prop_multinode_Sim :: ClientAndServerData Int Int Int -> MultiNodeScript Int Int Int TestAddr -> Property
prop_multinode_Sim serverData script' =
  simulatedPropertyWithTimeout 7200 $ do
    net <- newNetworkState (singletonScript noAttenuation) 10
    let snocket = mkSnocket net debugTracer
        script  = unTestAddr <$> script'
    counterexample (ppScript script) <$>
      multinodeExperiment snocket Snocket.TestFamily (Snocket.TestAddress 0) serverData script

ppScript :: (Show peerAddr, Show req, Show resp, Show acc) => MultiNodeScript peerAddr req resp acc -> String
ppScript (MultiNodeScript script) = intercalate "\n" $ go 0 script
  where
    delay (StartServer        d _ _) = d
    delay (StartClient        d _ _) = d
    delay (ClientConnection   d _)   = d
    delay (InboundNodeToNode  d _)   = d
    delay (OutboundNodeToNode d _)   = d

    ppEvent (StartServer        _ a p) = "Start server " ++ show a ++ " with " ++ ppData p
    ppEvent (StartClient        _ a p) = "Start client " ++ show a ++ " with " ++ ppData p
    ppEvent (ClientConnection   _ a)   = "Connection from client " ++ show a
    ppEvent (InboundNodeToNode  _ a)   = "Connection from server " ++ show a
    ppEvent (OutboundNodeToNode _ a)   = "Connecting to server " ++ show a

    ppData ClientAndServerData{responderAccumulatorFn = fn, accumulatorInit = i,
                               hotInitiatorRequests = hot,
                               warmInitiatorRequests = warm,
                               establishedInitiatorRequests = est} =
      concat ["fn:", show fn, "/", show i, " hot:", show hot, " warm:", show warm, " est:", show est]

    go _ [] = []
    go t (e : es) = printf "%5s: %s" (show t') (ppEvent e) : go t' es
      where t' = t + delay e

--
-- Utils
--

debugTracer :: (MonadSay m, MonadTime m, Show a) => Tracer m a
debugTracer = Tracer $
  \msg -> (,msg) <$> getCurrentTime >>= say . show


connectionManagerTracer
  :: ( MonadSay  m
     , MonadTime m
     , Show peerAddr
     , Show versionNumber
     , Show versionData
     )
  => Tracer m ( String
              , ConnectionManagerTrace peerAddr
                  (ConnectionHandlerTrace versionNumber versionData)
              )
connectionManagerTracer =
    Tracer
      $ \msg ->
        case msg of
          (_, TrConnectError{})
            -> -- this way 'debugTracer' does not trigger a warning :)
              traceWith debugTracer msg
          (_, TrConnectionHandler _ TrError {})
            ->
              traceWith debugTracer msg
          (_, _) ->
              pure ()


withLock :: ( MonadSTM   m
            , MonadThrow m
            )
         => StrictTMVar m ()
         -> m a
         -> m a
withLock v m =
    bracket (atomically $ takeTMVar v)
            (atomically . putTMVar v)
            (const m)

accFun :: Fun (Int, Int) (Int, Int)
accFun = Fun (function $ const (0, 0), (0, 0), unsafeCoerce True) (const (0, 0))

csData :: ClientAndServerData Int Int Int
csData = ClientAndServerData {responderAccumulatorFn = accFun, accumulatorInit = 0, hotInitiatorRequests = [],
                              warmInitiatorRequests = [], establishedInitiatorRequests = [[]]}

script :: MultiNodeScript Int Int Int TestAddr
script = MultiNodeScript [ StartServer 0 (TestAddr $ Snocket.TestAddress 17)
                              (ClientAndServerData {responderAccumulatorFn = accFun, accumulatorInit = 0, hotInitiatorRequests = [],
                                                    warmInitiatorRequests = [], establishedInitiatorRequests = [[]]})
                         , OutboundNodeToNode 2 (TestAddr $ Snocket.TestAddress 17)
                         , InboundNodeToNode 0 (TestAddr $ Snocket.TestAddress 17)]

simulatedPropertyWithTimeout :: DiffTime -> (forall s. IOSim s Property) -> Property
simulatedPropertyWithTimeout t test =
  exploreSimTrace 50 (timeout t $ exploreRaces >> test) $ \ tr ->
  counterexample ("\nTrace:\n" ++ ppTrace tr) $
  case traceResult False tr of
    Left failure ->
      counterexample ("Failure:\n" ++ displayException failure) False
    Right prop -> fromMaybe (counterexample "timeout" $ property False) prop
  -- where
  --   tr = runSimTrace $ timeout t test

ppTrace :: Trace a -> String
ppTrace tr = intercalate "\n" $ map fmt events
  where
    events = traceEvents tr
    w      = maximum [ length name | (_, _, Just name, _) <- events ]
    wtid   = maximum [ length (showTid tid) | (_, tid, _, _) <- events ]

    -- The hackery!!
    showTid tid
      | ids == [-1] = "(null)"
      | ids == []   = "root"
      | otherwise   = prefix ++ intercalate "." (map show ids)
      where
        s      = show tid
        isTest = "TestThreadId" `isPrefixOf` s
        n      = 1 + length (if isTest then "TestThreadId" else "ThreadId")
        prefix = if isTest then "t:" else "s:"
        ids    = read (drop n s) :: [Int]

    fmt (t, tid, lbl, e) = printf "%-10s - %-*s %-*s - %s" (show t) wtid (showTid tid) w (fromMaybe "" lbl) (show e)

