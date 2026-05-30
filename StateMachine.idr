||| PillPal Pro — Compartment Alert State Machine
||| Authors  : Bheesha & Ishaq Nasiru (PillPal)
||| Contact  : m26steph@uwaterloo.ca
||| Verified : Total, no holes, no believe_me
|||
||| This module defines the ONLY correct transitions between AlertStates.
||| The transition function is total and exhaustive: every (state, input)
||| pair has a defined output. No partial matches, no runtime panics.
module PillPal.Core.StateMachine

import PillPal.Types.Core
import PillPal.Types.Time

%default total

-- ---------------------------------------------------------------------------
-- Input events driving the state machine
-- ---------------------------------------------------------------------------

||| Events that can occur for a single compartment on each poll cycle.
public export
data Event : Type where
  ||| The lid is currently closed AND the deadline has not passed.
  EvIdle         : Event
  ||| The dose deadline has passed AND the lid is still closed.
  EvDueAndClosed : Event
  ||| The lid was opened WHILE the dose was due (correct usage).
  EvDueAndOpened : Event
  ||| The lid was opened BEFORE the dose was due (premature open).
  EvPrematureOpen : Event
  ||| The lid has been closed again after an angry event.
  EvLidReclosed  : Event

-- ---------------------------------------------------------------------------
-- State machine transition function
-- ---------------------------------------------------------------------------

||| The transition function for one compartment's alert state.
||| This is a pure, total function — it is the ground truth for what the
||| hardware and the web app must both agree on.
public export
transition : AlertState -> Event -> AlertState
-- From Idle
transition Idle  EvIdle          = Idle
transition Idle  EvDueAndClosed  = Alert
transition Idle  EvPrematureOpen = Angry
transition Idle  EvDueAndOpened  = Idle   -- shouldn't happen but safe
transition Idle  EvLidReclosed   = Idle

-- From Alert
transition Alert EvIdle          = Idle   -- time was reset externally
transition Alert EvDueAndClosed  = Alert
transition Alert EvDueAndOpened  = Taken
transition Alert EvPrematureOpen = Alert  -- already in alert; not angrier
transition Alert EvLidReclosed   = Alert

-- From Angry
transition Angry EvIdle          = Idle
transition Angry EvDueAndClosed  = Alert
transition Angry EvDueAndOpened  = Taken
transition Angry EvPrematureOpen = Angry
transition Angry EvLidReclosed   = Idle

-- From Taken
transition Taken EvIdle          = Taken  -- interval hasn't elapsed yet
transition Taken EvDueAndClosed  = Alert  -- next dose is due
transition Taken EvDueAndOpened  = Taken
transition Taken EvPrematureOpen = Angry
transition Taken EvLidReclosed   = Taken

-- ---------------------------------------------------------------------------
-- Event derivation from sensor readings
-- ---------------------------------------------------------------------------

||| Compute the event for a compartment given the current device state.
||| Pure and total: reads `now`, the config, and the lid state.
public export
deriveEvent :
    (now      : EpochTime) ->
    (cfg      : CompartmentConfig) ->
    (lidState : LidState) ->
    (current  : AlertState) ->
    Event
deriveEvent now cfg LidOpen   current =
  case isDue now cfg.takeTime of
    True  => EvDueAndOpened
    False => case current of
               Angry => EvPrematureOpen  -- stay angry; lid still open
               _     => EvPrematureOpen
deriveEvent now cfg LidClosed current =
  case isDue now cfg.takeTime of
    True  => EvDueAndClosed
    False => case current of
               Angry => EvLidReclosed
               _     => EvIdle

-- ---------------------------------------------------------------------------
-- Full state machine step — derives event then applies transition
-- ---------------------------------------------------------------------------

||| Advance one compartment by one poll cycle.
public export
step :
    (now     : EpochTime) ->
    (cfg     : CompartmentConfig) ->
    (lid     : LidState) ->
    (current : AlertState) ->
    AlertState
step now cfg lid current =
  let ev = deriveEvent now cfg lid current
  in transition current ev

-- ---------------------------------------------------------------------------
-- Proofs about the state machine
-- ---------------------------------------------------------------------------

||| Angry state is sticky while the lid remains open before deadline.
public export
angryIsSticky :
    (now : EpochTime) ->
    (cfg : CompartmentConfig) ->
    isDue now cfg.takeTime = False ->
    step now cfg LidOpen Angry = Angry
angryIsSticky now cfg notDue =
  rewrite notDue in Refl

||| Alert state self-loops while the lid is closed and dose is due.
public export
alertSelfLoops :
    (now : EpochTime) ->
    (cfg : CompartmentConfig) ->
    isDue now cfg.takeTime = True ->
    step now cfg LidClosed Alert = Alert
alertSelfLoops now cfg isDueTrue =
  rewrite isDueTrue in Refl

||| Opening the lid during Alert transitions to Taken.
public export
openDuringAlertTakesDose :
    (now : EpochTime) ->
    (cfg : CompartmentConfig) ->
    isDue now cfg.takeTime = True ->
    step now cfg LidOpen Alert = Taken
openDuringAlertTakesDose now cfg isDueTrue =
  rewrite isDueTrue in Refl

||| Idle is stable when nothing is due and lid is closed.
public export
idleIsStable :
    (now : EpochTime) ->
    (cfg : CompartmentConfig) ->
    isDue now cfg.takeTime = False ->
    step now cfg LidClosed Idle = Idle
idleIsStable now cfg notDue =
  rewrite notDue in Refl

-- ---------------------------------------------------------------------------
-- Reachability: from Idle, Alert is reachable only via EvDueAndClosed
-- ---------------------------------------------------------------------------

||| The only direct path from Idle to Alert is when a dose becomes due.
public export
idleToAlertRequiresDue :
    (ev : Event) ->
    transition Idle ev = Alert ->
    ev = EvDueAndClosed
idleToAlertRequiresDue EvIdle          prf = absurd prf
idleToAlertRequiresDue EvDueAndClosed  prf = Refl
idleToAlertRequiresDue EvDueAndOpened  prf = absurd prf
idleToAlertRequiresDue EvPrematureOpen prf = absurd prf
idleToAlertRequiresDue EvLidReclosed   prf = absurd prf

-- ---------------------------------------------------------------------------
-- No transition goes from Taken to Angry without a premature open
-- ---------------------------------------------------------------------------

public export
takenToAngryRequiresPremature :
    (ev : Event) ->
    transition Taken ev = Angry ->
    ev = EvPrematureOpen
takenToAngryRequiresPremature EvIdle          prf = absurd prf
takenToAngryRequiresPremature EvDueAndClosed  prf = absurd prf
takenToAngryRequiresPremature EvDueAndOpened  prf = absurd prf
takenToAngryRequiresPremature EvPrematureOpen prf = Refl
takenToAngryRequiresPremature EvLidReclosed   prf = absurd prf
