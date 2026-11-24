import YM.CF.BProof.Transit.Action
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay.C
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
open Hake Jet Sault Stax Sour
attribute [local instance] Sour.loreM Sour.loreN
open Rill Branch Tenant Drapes



open Levier Urn Ione
open Peaks


open Reed (Fine think)
open BProof Bide
variable {n:Type}[LinearOrder n][Fintype n] (b r:Bool)(U:UNI n){S X Y:Finset n}{A:FC n}{t:Bool}
lemma cigarette(i:n):windX b (put i)=put i:=by cases b;rfl; exact put_clear _
lemma cigar(i:n):windX b (takeF i)=takeF i:=by rw[takeF,win_s,cigarette]
lemma fumesF(g: Fine S X t A):Fine S X t (windX b A):=by
 induction g with
 | empty=>rw [win_z];apply Fine.empty
 | one=>rw [win_i];exact Fine.one
 | seed i h=>
   suffices v:windX b ((think S).term i)=(think S).term i from v.symm ▸ Fine.seed i h
   by_cases h':i∈S
   ·rw [show (think S).term i=put i from if_pos h',cigarette]
   rw [show (think S).term i= -takeF i from if_neg h']
   cases b;rfl;exact (cc_neg _).trans (congrArg Neg.neg (cigar true i))
 | scale _ c h=>rw [win_c];exact h.scale _
 | add _ _ f h=>rw[win_a];exact f.add h
 | grow _ _ f h=>rw [win_m];exact f.grow h

lemma fumes(g:Sector X t A):Sector X t (windX b A):= by
 induction g with
 | zero=>rw[win_z];apply Sector.zero
 | one=> rw[win_i];exact Sector.one
 | up i h=> rw[cigarette];exact Sector.up i h
 | down i h=> rw[cigar];exact Sector.down i h
 | scale _ c h=>rw [win_c];exact h.scale _
 | add _ _ f h=>rw[win_a];exact f.add h
 | mul _ _ f h=>rw [win_m];exact f.mul h
lemma toned (v:twist U (cutM S)=cutM S)(e:twist U (cutM X)=cutM Y)
 (g:Fine S X t A): Fine S Y t (twist (quantU U) A):=by
 have vc:twist U (cutM Sᶜ)=cutM Sᶜ:=by rw [dim_cut,map_sub,map_one,v]
 induction g with
 | empty=>rw[map_zero];apply Fine.empty
 | one=> rw[map_one];exact Fine.one
 | scale _ c h=> rw [twist_scalar];exact h.scale _
 | grow _ _ i j => rw [map_mul];exact i.grow j
 | add _ _ i j=>rw[map_add];exact i.add j
 | seed i h=>
   by_cases k:i∈S
   · rw [show (think S).term i=put i from if_pos k,twist_p]; apply Fine.sumF
     intro j _
     by_cases w:U.val j i=0
     ·rw [w,zero_smul];apply Fine.empty
     refine Fine.scale ?_ _
     have u:j∈Y:=by_contradiction (fun a=>w (Fine.entry e h a))
     have P:=Fine.seed (s:=S) _ u
     rw [show (think S).term j=put j from if_pos (by_contradiction (fun a=>w (Fine.entry v k a)))] at P
     exact P
   rw [show (think S).term i= -takeF i from if_neg k,map_neg,twist_t]
   suffices h0:Fine S Y true (prong takeF (cc U.val) i) from by simpa using h0.scale (-1)
   apply Fine.sumF;intro j _
   by_cases w:U.val j i=0
   ·simp only [cc_apply,w,star_zero,zero_smul];apply Fine.empty
   have u:j∈Y:=by_contradiction (fun a=>w (Fine.entry e h a))
   have P:=Fine.seed (s:=S) _ u
   have z:j∉S:=mem_compl.mp (by_contradiction (fun a=>w (Fine.entry vc (mem_compl.mpr k) a)))
   rw [show (think S).term j= -takeF j from if_neg z] at P
   exact (show Fine S Y true (takeF j) from by simpa using P.scale (-1)).scale _

lemma fumesC :windX b (cutM S)=cutM S:=by cases b;rfl;ext i j;by_cases h:i=j<;> simp [windX,cutM,h]

lemma fineTour (k:sings b U (cutM S)=swapX r (cutM S))(e:twist U (cutM X)=cutM Y)(g:Fine S X t A):
 Fine S Y t (Spire.tourP U b r A):=by
 rw [singT,fumesC] at k
 cases r
 · exact toned U k e (fumesF b g)
 exact Fine.arrive e (by rw [dim_cut,map_sub,map_one,k];change 1-(1-_)=_;abel) (fumesF b g)

lemma sceneTour (e:twist U (cutM X)=cutM Y)(g:Sector X t A):
 Sector Y t (Spire.tourP U b r A):= twist_sector r U (fumes b g) e

lemma starsTour (A:FC n):Spire.tourP U b r (star A)=star (Spire.tourP U b r A):=by
 cases r
 · change twist _ (windX b _) = _;rw [win_s,map_star];rfl
 change theta _ (windX b _) = _;rw [win_s,theta_star];rfl

lemma normTour (A:FC n): ‖Spire.tourP U b r A‖=‖A‖:=
 (pay_s r U (windX b A)).trans (by cases b; rfl;exact norm_cc _)
