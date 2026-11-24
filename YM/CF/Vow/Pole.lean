import YM.CF.Vow.Fair
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Trees Ursell Rue
variable {P:BudgetPoint}{F:Pax n} (A:Aura n)(K X':Cusp n)(V: Orbit n)
abbrev FeeD (P: BudgetPoint)(F:Pax n):Pax n:=fun i=> spinD P i F 0
abbrev coldE (P:BudgetPoint)(F:Pax n)(x: Orbit n) : Cipher n:=∑ i:Aura n with pingS P.threshold i.val x.1,F i x
abbrev beamP (P:BudgetPoint)(F:Cusp n)(x:Orbit n) :Cipher n:= Palot.Hac (flags P.threshold x.1) (hailV (flags P.threshold x.1) F x)
abbrev fuelV (P:BudgetPoint)(F:Cusp n)(x: Orbit n): Cipher n:=∑ i:Aura n with fuelH (flags P.threshold x.1) i,F i (flags P.threshold x.1 ∩ i.val) x
-- the CHARGE omitted in K is measured relative to final ok.Frame. account film norm. δ R arbitrary.
abbrev boastV (F:Pax n)(Q:Cusp n):Cusp n:=fun i D x=> exp (if D.Nonempty then Q i D x else - F i x)-1
local notation "Ω"=> flags P.threshold V.1
variable (Q:Aura n→ℝ)
variable {z q γ δ:ℝ}{B:ℕ}(p:Ready stern B Q a γ δ q)(hp:1≤h)(hv:∀ i, Medal P i.val ∅ (F i) h (Q i))(ha:0 ≤ a)(hz:FleetS P.threshold V.1)
include p hp hv ha hz
private lemma logA(y:Aura n)(t:Disjoint y.val Ω): Palot.jingle (Palot.halt (keyL P K F V) Ω) y= FeeD P F y V:=by
 have h:pingS P.threshold y.val V.1:= (shoreK _ _ hz _).mp t; rw [FeeD, Vow.spiritD _ V hp hv p ha (hates (show pingS P.threshold (y.val\∅) V.1 from by rw [sdiff_empty]; exact h))]; unfold jingle; apply tsum_congr; intro i; unfold sta; by_cases u:y=tideU i; swap; · rw [if_neg u,if_neg fun z=>u z.1]; rfl
 rw [if_pos u,if_pos ⟨u,Nat.zero_le _⟩]; unfold guava; simp only [Pi.smul_apply,Finset.prod_apply]; apply congrArg; refine prod_congr rfl fun j _=>?_ ; have ht:= Disjoint.mono_left (rimY i j) (show Disjoint (tideU i).val Ω from u ▸ t); unfold Palot.halt keyL; rw [if_pos (show Palot.constrainF Ω (i.2 j) from ht.symm),if_pos ht.symm]
private lemma tune_o (D:Support (More n))(h:Ω ⊆ D): Palot.south D (keyL P K F V)=exp (∑ i:Aura n with Disjoint i.val D, FeeD P F i V):=by
 let W:= keyL P K F V; let U':= Palot.halt W Ω; have he : Palot.south D W=Palot.south D U':=by apply Palot.south_at; intro j p v; exact p (if_pos (show constrainF Ω j from Disjoint.mono_left h v.symm)).symm -- tune
 rw [he]; have ht(y): ‖U' y‖ ≤ Q y :=by
    by_cases q: Disjoint Ω y.val; swap; · rw [show U' y=0 from if_neg q,norm_zero]; exact (hv y).wage (zero_le_one.trans hp)
    rw [show U' y=F y V from Eq.trans (if_pos (show constrainF Ω y from q)) (if_pos q)]; refine (hv y).capF hp _ ?_; rw [sdiff_empty]; exact (shoreK _ _ hz _).mp q.symm
 rw [Palot.sung D p ha ht]; apply congrArg; refine sum_congr rfl fun i u=>logA _ V Q p hp hv ha hz _ (Disjoint.mono_right h (mem_filter.mp u).2)
omit p hp hv ha
abbrev roomV (P: BudgetPoint) (F:Pax n)(K:Cusp n)(Q:Cusp n):= glowV K (boastV (FeeD P F) Q)
private lemma pactH (i:Palot.hook (Site (More n)))(v:i∈highV Ω): let D:=robe i; (∑ j:Aura n with Disjoint j.val D,FeeD P F j V)+fuelV P X' V=coldE P (FeeD P F) V+ ∑ s:Aura n with fuelH D s,(if (Ω∩s.val).Nonempty then hailV Ω X' V s else -FeeD P F s V):=by
 intro D; obtain ⟨u,w,h⟩:= (mem_filter.mp v).2; unfold coldE fuelV; rw [sum_filter,sum_filter,sum_filter,sum_filter, ←sum_add_distrib, ←sum_add_distrib]; apply sum_congr rfl; intro j _
 let q:= (shoreK _ _ hz j.val); have he :pingS P.threshold j.val V.1↔ Disjoint j.val Ω:=q.symm
 by_cases Z:Disjoint j.val Ω
 · rw [if_pos (he.mpr Z), if_neg (show ¬fuelH Ω j from not_not.mpr Z),if_neg (show ¬ (Ω∩j.val).Nonempty from fun h=> Finset.not_disjoint_iff_nonempty_inter.mpr h Z.symm),add_zero]; by_cases k:Disjoint j.val D; · rw [if_pos k, if_neg (show ¬ fuelH D j from not_not.mpr k), add_zero]
   rw [if_neg k, if_pos (show fuelH D j from k), add_neg_cancel] -- tune
 have ht:¬ Disjoint j.val D:=fun h=> Z (Disjoint.mono_right w h); rw [if_neg ht, if_pos (show fuelH Ω j from Z),if_neg (mt he.mp Z), if_pos (show fuelH D j from ht),if_pos (show (Ω∩j.val).Nonempty from Finset.not_disjoint_iff_nonempty_inter.mp fun v=>Z v.symm)]
private lemma appC (i:hook (Site (More n)))(t:i∈highV Ω) (F:Pax n): (∑ s:hook (Site (More n)) with raisedH (robe i) s,∏ j∈s, hailV Ω (boastV F X') V j) = exp (∑ j:Aura n with fuelH (robe i) j,(if (Ω ∩ j.val).Nonempty then hailV Ω X' V j else -F j V)):=by
 let W:=univ.filter (fuelH (robe i)); let Y(j):=hailV Ω (boastV F X') V j; letI:NormedAlgebra ℚ (Cipher n):= NormedAlgebra.restrictScalars ℚ ℝ _
 rw [show (univ.filter (raisedH (robe i)))= W.powerset from Finset.ext fun S=> ⟨fun h=>mem_powerset.mpr fun j q=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp h).2 _ q⟩,fun v=>mem_filter.mpr ⟨mem_univ _,fun j h=> (mem_filter.mp (mem_powerset.mp v h)).2⟩ ⟩,← Finset.prod_add_one, NormedSpace.exp_sum]; apply prod_congr rfl; intro y h; unfold hailV boastV; rw [sub_add_cancel]
include p hp hv ha
lemma whale : let U:=keyL P K F V; Palot.hGas Ω U*NormedSpace.exp (fuelV P X' V)=exp (coldE P (FeeD P F) V) * beamP P (roomV P F K X') V:=by
 intro U; let J:= hailV Ω K V; let W:=hailV Ω (boastV (FeeD P F) X') V; letI:NormedAlgebra ℚ (Cipher n):= NormedAlgebra.restrictScalars ℚ ℝ _
 rw [cloven, sum_mul,beamP, show hailV Ω (roomV P F K X') V= jack Ω J W from funext fun i=> pulpit ..,jab,mul_sum]; apply sum_congr rfl; intro i v; obtain ⟨r,t,u⟩:= (mem_filter.mp v).2; have hp': (∏ j∈i,U j)=∏ j∈i, J j:=prod_congr rfl fun j q=> if_neg fun g=> u j q g.symm
 rw [hp', show south (robe i) U= _ from tune_o K V Q p hp hv ha hz (robe i) t,mul_assoc, ←exp_add,pactH X' V hz i v,exp_add,show ∑ s:hook (Site (More n)) with raisedH (robe i) s, _ =_ from appC X' V hz i v (FeeD P F)] -- tune order
 ring -- tune fuelV sign! here left times +∆ right uses X' DOUBLE? tactic identifies sign
lemma polyH (Y: Cipher n)(s: Y+fuelV P X' V=coldE P (FeeD P F) V): Palot.hGas Ω (keyL P K F V)=NormedSpace.exp Y*beamP P (roomV P F K X') V:=by
 letI:NormedAlgebra ℚ (Cipher n):= NormedAlgebra.restrictScalars ℚ ℝ _; let O:= fuelV P X' V; set Q':= hGas Ω (keyL P K F V); let W:= beamP P (roomV P F K X') V
 have he : Q' *exp O= exp (coldE P (FeeD P F) V) * W := whale K X' V Q p hp hv ha hz; have hg:exp O* exp (-O)=1:=by rw [← exp_add,add_neg_cancel,exp_zero ]
 rw [← s, exp_add, show fuelV P X' V= _ from (rfl:fuelV P X' V=O)] at he
 calc
   _ = Q'*exp O * exp (-O):=by rw [mul_assoc,hg,mul_one]
   _ = NormedSpace.exp Y*(exp O*exp (-O))* W:=by rw [he]; ring
   _ = _:=by rw [hg,mul_one]
end YM.CF.Vow
