module Task.Examples

import Helpers
import Task.Syntax

-- These imports are a convenience for the Repl
import Data.Fuel
import Task.Simulate

Guard : List (Symbolic Bool, Task h (Symbolic a)) -> Task h (Symbolic a)
Guard [] = Fail
Guard ((b, t) :: ts) = Test b t (Guard ts)

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
