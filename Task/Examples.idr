module Task.Examples

import Helpers
import Task.Symbolic.Syntax

-- These imports are a convenience for the Repl
import Data.Fuel
import Task.Simulate

Guard : List (Symbolic Bool, Task h (Symbolic a)) -> Task h (Symbolic a)
Guard [] = Fail
Guard ((b, t) :: ts) = Test b t (Guard ts)

Continue : Task h (Symbolic a') -> (Symbolic a' -> Task h (Symbolic a)) -> Task h (Symbolic a)
Continue t1 e2 = t1 `Step` \x => Edit Unnamed (Select ["Continue" ~> e2 x])

---- Absolute value ------------------------------------------------------------

absolute : Task None (Symbolic Int)
absolute =
  Edit Unnamed Enter `Step` \x =>
  Guard [ x >. Value 0 ~> Edit Unnamed (View x) ]

---- Subsidy request -----------------------------------------------------------

Amount : Type
Amount = Symbolic Int

Affirmation : Type
Affirmation = Symbolic Bool

Date : Type
Date = Symbolic Int

requestSubsidy : Task None Amount
requestSubsidy =
  let
    today : Date
    today = Value 321

    provideDocuments : Task None (Symbolic (Int, Int))
    provideDocuments = Edit Unnamed Enter `Pair` Edit Unnamed Enter

    companyConfirm : Task None Affirmation
    companyConfirm = Edit Unnamed (Select [
      "Confirm" ~> Done (Value True),
      "Deny" ~> Done (Value False)
    ])

    officerApprove : Date -> Date -> Affirmation -> Task None Affirmation
    officerApprove invoiced date confirmed =
      Edit Unnamed (Select [
        "Approve" ~> Test (date -. invoiced <. Value 365 &&. confirmed)
          (Done (Value True))
          (Fail),
        "Reject" ~> Done (Value False)
      ])
  in
  (provideDocuments `Pair` companyConfirm) `Step` unwrap >> \(pair, confirmed) =>
  let (expenses, invoiced) = unwrap pair in
  officerApprove invoiced today confirmed `Step` \approved =>
  let subsidy = ite approved (min (Value 600) (expenses /. Value 10)) (Value 0) in
  Assert (subsidy >=. Value 0 ==>. confirmed) `Step` \_ =>
  Assert (subsidy >.  Value 0 ==>. approved)  `Step` \_ =>
  Assert (approved ==>. confirmed &&. today -. invoiced <. Value 365) `Step` \_ =>
  Assert (subsidy <=. Value 600) `Step` \_ =>
  Assert (Not approved ==>. subsidy ==. Value 0) `Step` \_ =>
  Edit Unnamed (View subsidy)

---- Computer scientists -------------------------------------------------------

Availability : Type
Availability = Symbolic Bool

Nil : Type
Nil = Symbolic ()

Result : Type
Result = Symbolic String

computerScientists : Task Triple Result
computerScientists =
  let
    pickup : Ref Triple Availability -> Ref Triple Availability -> Task Triple Nil
    pickup this that =
      Edit Unnamed (Watch this) `Step` \thisup =>
      Test thisup (
        Assign (Value False) this `Step` \_ =>
        Edit Unnamed (Watch that) `Continue` \thatup =>
        Test thatup (
          Assign (Value True) this
        ) (
          Fail
        )
      ) (
        Fail
      )
    scientist : String -> Ref Triple Availability -> Ref Triple Availability -> Task Triple (Symbolic (String, ()))
    scientist name left right =
      Edit Unnamed (View (Value name)) `Pair` (Edit Unnamed (Select
        [ "Left"  ~> pickup left right
        , "Right" ~> pickup right left
        ]))
    fork0 : Ref Triple Availability
    fork0 = Idx 0
    fork1 : Ref Triple Availability
    fork1 = Idx 1
    fork2 : Ref Triple Availability
    fork2 = Idx 2
  in
  (scientist "Alan" fork0 fork1 `Pair` (scientist "Grace" fork1 fork2 `Pair` scientist "Ada" fork2 fork0)) `Step` \_ =>
  Done (Value "Full bellies")
