import SatinThinLevy
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance
variable (i k:ℕ) {P' V: Side} {f r v t m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "K"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
/- Actual-path Lease of Parliament: convoy and roots. Any number of supports. No stencils in cutoff budgets before size. -/
section rec
variable {X:ℕ→ Sort _}(E: ∀ i:ℕ,X i → X (i+1))
def climbing (p:f ≤ v) (x:X f) : X v:= Nat.leRec (motive:=fun m _=> X m) x (fun {_} _ t=> E _ t) p -- Nat autoImplicit k, implicit `fun {k}`
lemma climbing_refl (x:X f): climbing E (Nat.le_refl f) x=x:=by rw [climbing,Nat.leRec_self]
lemma climbing_succ (x:X f)(p:f ≤ v) :climbing E (v:=v+1) (by omega) x= E v (climbing E p x) := by unfold climbing; rw [Nat.leRec_succ _ _ p]
lemma climbing_trans (x:X f)(p:f ≤ v)(q:v ≤ m): climbing E (p.trans q) x=climbing E q (climbing E p x):=by
 induction q with | refl=> rw [climbing_refl] | step h ih=> rw [climbing_succ E _ (p.trans h),climbing_succ E _ h,ih]
lemma climbing_step (x:X f)(p:f < v) : climbing E p.le x= climbing E p (E f x) :=by rw [climbing_trans E x (Nat.le_succ f) (show f+1 ≤ v from p),climbing_succ E x (Nat.le_refl f), climbing_refl]
end rec
abbrev convoy (z:f≤v): Mark (Ω f)→ Mark (Ω v) := climbing (X:=fun j=> Mark (Ω j)) (fun j=> ascender Y j i k) z
abbrev upRoot (z:f≤v): Site (Ω f) → Site (Ω v):=climbing (fun j=> heel (Vale.apt (Y.ir i) P.block P.R.L j)) z
-- no use wn
abbrev upMark (z:f ≤ v):ℕ→ℕ:=climbing (X:=fun _=>ℕ) (fun _=>grantRadius P ℓ) z
local notation:max "H" p:max=> upRoot Y i p
local notation:max "C" p:max=> convoy Y i k p
local notation "E" p:max=> upMark (P:=P) (ℓ:=ℓ) p
variable {I:Type} [DecidableEq I]
variable (o:I→Site (side Y i f))(F:I→ Mark (side Y i f))
lemma beyond_clasp (x: f≤v)(p: Beyond P ℓ o a): Beyond P ℓ (H x ∘ o) (upMark (P:=P) (ℓ:=ℓ) x a):=by
 induction x with
 | refl=>rwa [show (H (Nat.le_refl f)) = _root_.id from funext fun _=> climbing_refl .., id_comp, upMark,climbing_refl]
 | step x ih=>
    intro u v y; simp only [upMark, upRoot,Function.comp_apply, climbing_succ _ _ x]; exact heel_range Y _ ih u v y
variable (p:(Y.voyage i).kick ≤ k){X:Mark (side Y i f)}
include p
lemma convoy_all (u:f ≤ v)(t:v≤ Y.uv k)(e:AtSupport false univ X): AtSupport false univ (C u X):=by
 induction u with|refl=>rw [convoy,climbing_refl]; exact e|step h ih=> rw [convoy, climbing_succ _ _ h]; exact weight_all Y i k (ih (by omega)) ⟨p,t⟩
lemma convoy_one (u:f≤ v)(t:v ≤ Y.uv k): C u 1=1:=by
 induction u with|refl=>exact climbing_refl ..| step h ih=> rw [convoy,climbing_succ _ _ h]; unfold convoy at ih; rw [ih (by omega)]; exact ascendUnit Y _ i k ⟨p,t⟩
lemma convoy_add {X': Mark (Ω f)} (e:AtSupport false univ X)(e':AtSupport false univ X')(u:f ≤ v)(t:v ≤ Y.uv k): C u (X+X')= C u X+ C u X':=by
 induction u with|refl=> simp only [convoy,climbing_refl]| step h ih=> simp only [convoy, climbing_succ _ _ h]; unfold convoy at ih; rw [ih (by omega)]; exact ascendPlus Y _ _ _ ⟨p,t⟩ _ _ (convoy_all Y i k p h (by omega) e).env (convoy_all Y i k p h (by omega) e').env
lemma convoy_scale (e:AtSupport false univ X)(q:ℂ)(u:f ≤ v)(t:v ≤ Y.uv k): C u (q • X)= q • C u X:=by
 induction u with|refl=>simp only [convoy,climbing_refl]|step h ih=>simp only [convoy, climbing_succ _ _ h]; unfold convoy at ih; rw [ih (by omega)]; exact ascendScale Y _ _ _ ⟨p,t⟩ _ (convoy_all Y i k p h (by omega) e).env _
lemma convoy_fat(x:Site (Ω f))(e:AtSupport false (fatAt x a) X)(u:f ≤ v)(t:v≤ Y.uv k): AtSupport false (fatAt (H u x) (upMark (P:=P) (ℓ:=ℓ) u a)) (C u X):=by
 induction u with|refl=>simp only [upRoot,upMark,convoy,climbing_refl]; exact e| step h ih=>rw [convoy,upMark,upRoot, climbing_succ _ _ h,climbing_succ _ _ h,climbing_succ _ _ h]; exact (weight Y _ _ ⟨p,t⟩ 0 (ih (by omega))).mono (padding Y _ _)
lemma convoy_product (u:f ≤ v)(t:v ≤ Y.uv k)(z:Beyond P ℓ o a)(e:∀i, AtSupport false (fatAt (o i) a) (F i))(l:List I)(v:l.Nodup): C u (l.map F).prod=(l.map (C u ∘ F)).prod:=by
 induction u with
 | refl=> rw [show C (Nat.le_refl f)= _root_.id from funext fun _=> climbing_refl ..,id_eq,id_comp]
 | @step m h ih=>
    let p':Satin.PairIdx Y m i k:=⟨p,t⟩; rw [show C (show f ≤ m+1 from Nat.le.step h)= (ascender Y m i k) ∘ C h from funext fun i=> climbing_succ _ _ h, Function.comp_apply, ih (by omega), follow_cost Y _ _ p' (H h∘o) (C h∘F) (beyond_clasp Y i o h z) (fun i=> convoy_fat Y _ _ p (o i) (e i) h (by omega)) l v]
    rfl
lemma ring_tour (u:f ≤ v)(t:v≤ Y.uv k)(i':Axis)(z:ℤ)(e:AtSupport false univ X): C u (reflMark i' z X)= reflMark i' (((L).val:ℤ)^(v-f)*z) (C u X):=by
 induction u with
 | refl=> simp only [convoy,climbing_refl,Nat.sub_self,pow_zero,one_mul]
 | step h ih=> simp only [convoy,climbing_succ _ _ h]; unfold convoy at ih; rw [ih (by omega),ascendTurn Y _ i k i' _ ⟨p,t⟩ (convoy_all Y _ _ p h (by omega) e),Nat.succ_sub h,pow_succ',mul_assoc] -- tuning
-- panorama foot beyond costs earned all depths
omit p
lemma waist (v: ℕ) : Tendsto (fun m=>(Y.meter.a m).B) atTop atTop:=by
 let q(m:ℕ):=radiusB (hat P.R.L P.x m); have e(m:ℕ): (Y.meter.a m).B=q m:= (Y.meter.boot m).2.1
 simp_rw [e]; exact Work.E01.radiusB_tendsto.comp (turnover P) -- radiusB unknown direction
lemma gather_at (a:ℕ): ∀ᶠ f:ℕ in atTop, ∀ (I:Type) [DecidableEq I] (i k:ℕ), f≤Y.uv k→∀ o:I→Site (side Y i f), Very_Ψ o (RootBook Y i k f).p.B → Beyond P ℓ o a:=by
 filter_upwards [(waist Y 0).eventually_ge_atTop (2*a+4*Levy P ℓ)] with f p I _ i k hp o v x y h
 have hx:= v.2 _ _ (v.1.ne h); change _ < separation (node (o x)) (node (o y)) at hx
 have hh:(Y.meter.a f).B=(RootBook Y i k f).p.B:= congrArg BudgetPoint.B (((Y.voyage i).X (Y.uv k)).pull.owns f hp).width
 rw [hh] at p; omega
omit [DecidableEq I] in
lemma send_at [Fintype I][LinearOrder I] (L':10≤P.R.L.val)(u:f ≤ v)(p: Very_Ψ o (RootBook Y i k f).p.B)(t:v≤Y.uv k): Very_Ψ (H u∘o) (RootBook Y i k v).p.B:=by
 induction u with | refl=> rwa [show H (Nat.le_refl f)= _root_.id from funext fun _=> climbing_refl ..,id_comp]| @step m h ih=> rw [show H (show f ≤ m+1 from Nat.le.step h)= (heel (Gξ m)) ∘ H h from funext fun _=> climbing_succ _ _ h]; exact sprint_B Y _ _ _ t L' _ (ih (by omega))
-- send_at above needs Fintype I&LinearOrder I in sprint_B, remove decidableEq
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
