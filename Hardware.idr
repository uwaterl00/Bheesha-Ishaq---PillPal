||| PillPal Pro — ESP32 Hardware Type Definitions
||| Authors  : Bheesha Ramachandran & Ishaq Nasiru (PillPal)
||| Contact  : m26steph@uwaterloo.ca
||| Verified : Total, no holes, no believe_me
module PillPal.Types.Hardware

import PillPal.Types.Core

%default total

-- ---------------------------------------------------------------------------
-- GPIO pin numbers, bounded to valid ESP32 range [0..39]
-- ---------------------------------------------------------------------------

||| An ESP32 GPIO pin number, statically constrained to [0..39].
public export
data GpioPin : (n : Nat) -> Type where
  MkPin : (n : Nat) -> {auto 0 inRange : n `LTE` 39} -> GpioPin n

||| Extract the raw pin number from a GpioPin.
public export
pinNumber : GpioPin n -> Nat
pinNumber (MkPin n) = n

-- ---------------------------------------------------------------------------
-- Concrete pin assignments (matching PillBoxCode.ino exactly)
-- ---------------------------------------------------------------------------

public export
buttonPin1 : GpioPin 26
buttonPin1 = MkPin 26

public export
buttonPin2 : GpioPin 25
buttonPin2 = MkPin 25

public export
buttonPin3 : GpioPin 33
buttonPin3 = MkPin 33

public export
buttonPin4 : GpioPin 32
buttonPin4 = MkPin 32

public export
ledPin1 : GpioPin 13
ledPin1 = MkPin 13

public export
ledPin2 : GpioPin 12
ledPin2 = MkPin 12

public export
ledPin3 : GpioPin 14
ledPin3 = MkPin 14

public export
ledPin4 : GpioPin 27
ledPin4 = MkPin 27

public export
buzzerPin : GpioPin 15
buzzerPin = MkPin 15

-- ---------------------------------------------------------------------------
-- PWM configuration
-- ---------------------------------------------------------------------------

||| PWM resolution in bits, must be 1..16 on ESP32.
public export
data PwmResolution : (bits : Nat) -> Type where
  MkPwmRes : (bits : Nat) ->
             {auto 0 lower : 1 `LTE` bits} ->
             {auto 0 upper : bits `LTE` 16} ->
             PwmResolution bits

||| 8-bit PWM resolution (as used in PillBoxCode.ino).
public export
pwmRes8 : PwmResolution 8
pwmRes8 = MkPwmRes 8

||| Maximum duty cycle value for a given PWM resolution.
public export
maxDuty : PwmResolution bits -> Nat
maxDuty (MkPwmRes bits) = (power 2 bits) `minus` 1

||| Proof: maxDuty 8-bit resolution is 255.
public export
maxDuty8Is255 : maxDuty pwmRes8 = 255
maxDuty8Is255 = Refl

||| A PWM duty value bounded to [0 .. maxDuty].
public export
record DutyCycle (res : PwmResolution bits) where
  constructor MkDuty
  value    : Nat
  inBounds : value `LTE` maxDuty res

||| Zero duty (LED/buzzer off).
public export
zeroDuty : (res : PwmResolution bits) -> DutyCycle res
zeroDuty res = MkDuty 0 (LTEZero)

||| Full duty (LED/buzzer at maximum brightness/volume).
public export
fullDuty : (res : PwmResolution bits) -> DutyCycle res
fullDuty res = MkDuty (maxDuty res) lteRefl

-- ---------------------------------------------------------------------------
-- PWM channel assignments (mirroring PillBoxCode.ino)
-- ---------------------------------------------------------------------------

||| ESP32 LEDC channels, 0..15.
public export
data LedcChannel : (ch : Nat) -> Type where
  MkChannel : (ch : Nat) -> {auto 0 ok : ch `LTE` 15} -> LedcChannel ch

public export
buzzerChannel : LedcChannel 0
buzzerChannel = MkChannel 0

public export
ledChannel1 : LedcChannel 1
ledChannel1 = MkChannel 1

public export
ledChannel2 : LedcChannel 2
ledChannel2 = MkChannel 2

public export
ledChannel3 : LedcChannel 3
ledChannel3 = MkChannel 3

public export
ledChannel4 : LedcChannel 4
ledChannel4 = MkChannel 4

-- ---------------------------------------------------------------------------
-- Button state
-- ---------------------------------------------------------------------------

||| Physical lid state, read from a pull-up GPIO.
||| HIGH (True) = lid open; LOW (False) = lid closed (pull-up default).
public export
data LidState : Type where
  LidOpen   : LidState
  LidClosed : LidState

public export
Eq LidState where
  LidOpen   == LidOpen   = True
  LidClosed == LidClosed = True
  _         == _         = False

public export
Show LidState where
  show LidOpen   = "Open"
  show LidClosed = "Closed"

||| Map a compartment to its hardware button pin.
public export
buttonPinFor : (cid : CompartmentId) -> (n : Nat ** GpioPin n)
buttonPinFor C1 = (26 ** buttonPin1)
buttonPinFor C2 = (25 ** buttonPin2)
buttonPinFor C3 = (33 ** buttonPin3)
buttonPinFor C4 = (32 ** buttonPin4)

||| Map a compartment to its LED pin.
public export
ledPinFor : (cid : CompartmentId) -> (n : Nat ** GpioPin n)
ledPinFor C1 = (13 ** ledPin1)
ledPinFor C2 = (12 ** ledPin2)
ledPinFor C3 = (14 ** ledPin3)
ledPinFor C4 = (27 ** ledPin4)

||| Map a compartment to its LEDC channel.
public export
ledChannelFor : (cid : CompartmentId) -> (ch : Nat ** LedcChannel ch)
ledChannelFor C1 = (1 ** ledChannel1)
ledChannelFor C2 = (2 ** ledChannel2)
ledChannelFor C3 = (3 ** ledChannel3)
ledChannelFor C4 = (4 ** ledChannel4)

-- ---------------------------------------------------------------------------
-- Volume modifier (matching #define VOL_MOD 0.1 in PillBoxCode.ino)
-- ---------------------------------------------------------------------------

||| Volume modifier: buzzer duty is scaled by 1/10.
||| Represented as a ratio to avoid floating-point in the type system.
public export
record VolumeRatio where
  constructor MkVolumeRatio
  numerator   : Nat
  denominator : Nat
  {auto 0 nonZero : IsSucc denominator}

public export
volMod : VolumeRatio
volMod = MkVolumeRatio 1 10

||| Apply volume modifier to a raw duty value.
public export
applyVolume : VolumeRatio -> Nat -> Nat
applyVolume (MkVolumeRatio n d) duty = (duty * n) `div` d
