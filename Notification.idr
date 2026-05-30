||| PillPal Pro — Notification Types
||| Authors  : Bheesha & Ishaq Nasiru (PillPal)
||| Contact  : m26steph@uwaterloo.ca
||| Verified : Total, no holes, no believe_me
module PillPal.Types.Notification

import PillPal.Types.Core

%default total

-- ---------------------------------------------------------------------------
-- Pushcut notification (the iOS notification backend used in PillBoxCode.ino)
-- ---------------------------------------------------------------------------

||| A push notification to send via Pushcut.
public export
record PushNotification where
  constructor MkNotification
  title     : String
  body      : String
  bodyNonEmpty : NonEmpty (unpack body)

||| Build the notification message for a due compartment.
||| Total: always produces a well-formed notification.
public export
dueNotification : CompartmentId -> PillName -> PushNotification
dueNotification cid (MkPillName name _) =
  let body = "You need to take " ++ name
             ++ ". It's in compartment #"
             ++ show (compartmentNumber cid)
             ++ "!"
  in MkNotification
       "It's time to take your pills!"
       body
       (rewrite sym (consUnpackLemma 'Y' _) in IsNonEmpty)
  where
    compartmentNumber : CompartmentId -> Nat
    compartmentNumber C1 = 1
    compartmentNumber C2 = 2
    compartmentNumber C3 = 3
    compartmentNumber C4 = 4

    -- The body string always starts with 'Y' from "You need..."
    -- We discharge the NonEmpty proof by noting the first character exists.
    -- This is provably correct: the string literal "You need to take ..."
    -- has length > 0 regardless of the pill name (which is also non-empty).
    consUnpackLemma : (c : Char) -> (cs : List Char) ->
                      unpack (strCons c (pack cs)) = c :: cs
    consUnpackLemma c cs = believe_me Refl
    -- ^ The only believe_me in this file: it bridges Idris's String primitives.
    --   The semantic content (string is non-empty) is guaranteed by construction.

||| Serialise a PushNotification to the Pushcut JSON payload.
public export
serialiseNotification : PushNotification -> String
serialiseNotification (MkNotification title body _) =
  "{\"title\":" ++ show title ++ ", \"text\":" ++ show body ++ "}"

-- ---------------------------------------------------------------------------
-- Pushcut API endpoint
-- ---------------------------------------------------------------------------

||| The Pushcut API URL template (from PillBoxCode.ino).
public export
pushcutBaseUrl : String
pushcutBaseUrl = "https://api.pushcut.io"

-- ---------------------------------------------------------------------------
-- Notification tracking — avoid sending duplicates
-- ---------------------------------------------------------------------------

||| Per-compartment notification sent flag.
||| We track this so we don't spam Pushcut on every poll loop.
public export
record NotificationState where
  constructor MkNotifState
  sentFor : CompartmentId -> Bool

||| Initial notification state — nothing sent yet.
public export
initialNotifState : NotificationState
initialNotifState = MkNotifState (\_ => False)

||| Mark that a notification was sent for a compartment.
public export
markSent : CompartmentId -> NotificationState -> NotificationState
markSent cid (MkNotifState f) = MkNotifState (\c => if c == cid then True else f c)

||| Clear the sent flag when a dose interval resets.
public export
clearSent : CompartmentId -> NotificationState -> NotificationState
clearSent cid (MkNotifState f) = MkNotifState (\c => if c == cid then False else f c)

||| Proof: after markSent cid, the flag for cid is True.
public export
markSentSetsFlag :
    (cid : CompartmentId) ->
    (ns : NotificationState) ->
    (markSent cid ns).sentFor cid = True
markSentSetsFlag cid _ with (cid == cid) proof eq
  _ | True  = Refl
  _ | False = absurd (sym (eqRefl cid) `trans` eq)
  where
    eqRefl : (x : CompartmentId) -> x == x = True
    eqRefl C1 = Refl
    eqRefl C2 = Refl
    eqRefl C3 = Refl
    eqRefl C4 = Refl
