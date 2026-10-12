import BanditRLProof.OnlineStrongConvexSourceSubgradient
import BanditRLProof.OnlineStrongConvexMinimum
import WeierstrassExtendedCandidate
import Mathlib.Analysis.Normed.Module.FiniteDimension

import Lean.Util.FoldConsts

noncomputable section
open Set
namespace BanditRL.OnlineConvex

end BanditRL.OnlineConvex

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut origins : Array Json := #[]
  for n in env.header.moduleNames do
    let file ← liftIO <| findOLean n
    origins := origins.push <| Json.mkObj [("module",toJson n.toString),("olean",toJson file.toString)]
  liftIO do
    let out ← IO.FS.Handle.mk "tmp/online-b4-next-attainment-body-20261012/header-import-origins-v2.json" .writeNew
    out.putStr ((toJson origins).pretty ++ "\n")
