import YM.CF.Wray.Shop
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Wray
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Iva Eire Trees
local notation "c₀"=> Domain N B
local notation "f₀"=> Domain P B
local notation "t_"=> mid P B
variable (vη: Rust (mid P B)→ℝ)(C: Rust (mid P B)→ Raid (LeanV (Single (mid P B))))
local notation "R"=> rustL t_
abbrev angle (i:Rust (mid P B)):= (rustL (mid P B) i).val.1
abbrev shaft (i:Rust (mid P B)):= (rustL (mid P B) i).val.2
structure Rustic (p:BudgetPoint)(A: Rust (mid P B)→ℝ)(Q: Rust (mid P B)→Raid (LeanV (Single (mid P B)))) (h γ:ℝ): Prop where
 cash:0 ≤ Q
 cup(i:Rust (mid P B)) : (∑ j:Finset (Dwell (mid P B)),Scree.tariff p (angle i) h j * Q i j) ≤ A i
 art(i:Seat (mid P B)): (∑ x: Rust (mid P B) with angle x=i,p.mass (shaft x) (A x)) ≤ γ
lemma Rustic.shaftZ{p: BudgetPoint}{d γ:ℝ}(U:Rustic p vη C d γ)(q:ℝ)(w:0≤q)(x:q ≤ d)(i:Rust (mid P B)): 0≤vη i ∧ joinV (stake q) (C i) ≤ vη i∧ vη i ≤ γ:=by
 have ht(j:Finset (Dwell t_))(o:Seat t_): stake q j ≤ Scree.tariff p o d j:=by unfold stake Scree.tariff; apply (pow_le_pow_left₀ w x _).trans; exact le_mul_of_one_le_left (pow_nonneg (w.trans x) _) (one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _)))
 have hx(j:Rust t_): joinV (stake q) (C j) ≤ vη j:= le_trans (sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (ht i _) (U.cash j i))) (U.cup j)
 have hz(j:Rust t_): 0 ≤ joinV (stake q) (C j):=sum_nonneg (fun i _=> mul_nonneg ((stokes (X:=LeanV (Single t_)) w).fee i) (U.cash _ _))
 let v(j:Rust t_):=p.mass (shaft j) (vη j); have hr(j:Rust t_):vη j ≤ v j:=p.loMass _ _ ((hz j).trans (hx j)); have hv(j:Rust t_):0 ≤ v j:= (hz j).trans ((hx j).trans (hr j))
 refine ⟨(hz i).trans (hx i),hx i,(hr i).trans (le_trans ?_ (U.art (angle i)))⟩; change v i ≤ ∑ x:Rust t_ with angle x=angle i,v x; exact single_le_sum (f:=v) (fun i _=>hv i) (mem_filter.mpr ⟨mem_univ i,rfl⟩)
lemma banner_h{X:Type}[Fintype X][LinearOrder X](B:Raid X)(p:0 ≤ B)(w:Finset X)(h:0 ≤ d): loadH (postY w B) d ≤ joinV (stake d) B:=by
 let X' := Pastry.Wheat w; unfold loadH; change (∑ i:X',B i.val*d^(Finset.sort i.val (· ≤ ·)).length) ≤ _; simp_rw [Finset.length_sort,mul_comm (B _)]; rw [Finset.sum_coe_sort X' (fun i:Finset X=>d^i.card * B i)]; exact sum_le_sum_of_subset_of_nonneg (subset_univ X') fun i _ _=>mul_nonneg (pow_nonneg h _) (p _)
-- polish income. Masks factors polynomial cover and B only.
def rateV(M _n:ℕ):= (M+M+1)^4*50^4*Fintype.card PlaqAxes
lemma countY (i:Rust (mid P B))(M:ℕ): (inspectD (shaft i)).card ≤ rateV M k * coverNumber M (shaft i):=by
 let Q:=shaft i; apply (Cloak.pack_y Q).trans; apply (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Corona.pays Q M))).trans; dsimp only [Q,rateV ]; apply Eq.le; ac_rfl -- inequality
local notation "η"=> Rust (mid P B)
def gleam (T D v:ℝ)(k M:ℕ):= Rue.ξ k (priceK k (rateV M k) D) * (Real.exp (Rue.θ v k*T) * Rue.θ v k)
lemma myPrice (p:BudgetPoint)(A:Rustic p vη C d t)(q:ℝ)(w:0 ≤ q)(u:q≤d)(v D:ℝ)(x:0 ≤ v)(T:ℝ)(e:t≤T)(i:Rust (mid P B))(hX:0 ≤ gift_k i (C i) v D k):loadH (postY (camp (shaft i)) (gift_k i (C i) v D k)) q ≤ gleam T D v k p.B * vη i * (1+(coverNumber p.B (shaft i):ℝ))^k:=by
 obtain ⟨r,z,b'⟩:= A.shaftZ vη C q w u i; apply (banner_h _ hX _ w).trans
 unfold gift_k; dsimp only; rw [subsidY]; let M:= coverNumber p.B (shaft i); let Y:= rateV p.B k; have he:0 ≤ Rue.θ v k:=mul_nonneg (by positivity) x; have hp:0 ≤ T:= (r.trans b').trans e; let MX:= inspectD (rustL (mid P B) i).val.2
 let L':=Rue.ξ k (Cloak.priceK k Y D); set LX:= Rue.ξ k (priceK k MX.card D) with def1; have hh: LX ≤ L'*(1+(M:ℝ))^k:=by
    unfold LX L' Rue.ξ Cloak.priceK; calc
      _ ≤ ‖Rue.φC‖*((k.factorial:ℝ)* Real.exp (k*D)*((1+(Y:ℝ))*(1+M:ℝ))^k)* (k+1:ℝ):=by
          gcongr; have he: (MX.card:ℝ) ≤ (Y:ℝ)*M:= by exact_mod_cast countY (k:=k) i p.B
          have ht:0≤(M:ℝ):=Nat.cast_nonneg _; linarith [Nat.cast_nonneg (α:=ℝ) Y]
      _ = _:=by rw [mul_pow]; ring
 let C':=(C i); have hu: 0≤ Rue.θ v k • C':=smul_nonneg he (A.cash i); let b:= vη i; have hb:joinV (stake q) (Rue.θ v k • C') ≤ Rue.θ v k*b:=by rw [subsidY]; exact mul_le_mul_of_nonneg_left z he
 have hL:0 ≤ LX:=by unfold LX Rue.ξ Cloak.priceK; positivity
 let Ω:= Real.exp (Rue.θ v k*T)*(Rue.θ v k*b); have hf:joinV (stake q) (Sum.elim (fun _=> Rue.saber (Rue.θ v k • C') 1) (fun _=> Rue.θ v k • C') i) ≤ Ω:=by
    by_cases hu': i.isLeft; · have hk:= Rue.peony (u:=Rue.θ v k • C') 1 hu (stokes w); have hk':joinV (stake q) (Rue.saber (Rue.θ v k • C') 1)≤ Ω:=(hk.trans (by rw [pow_one]; have hv:0 ≤ joinV (stake q) (Rue.θ v k • C'):= sum_nonneg (fun i _=> mul_nonneg (pow_nonneg w _) (hu i)); exact mul_le_mul (Real.exp_monotone (hb.trans (mul_le_mul_of_nonneg_left (b'.trans e) he))) hb hv (Real.exp_pos _).le)); cases i<;>simp_all
    have hh: joinV (stake q) (Rue.θ v k • C')≤ Ω:=hb.trans (le_mul_of_one_le_left (mul_nonneg he r) (Real.one_le_exp (mul_nonneg he hp))); cases i <;>simp_all
 exact (mul_le_mul_of_nonneg_left hf hL).trans ((mul_le_mul_of_nonneg_right hh (mul_nonneg (Real.exp_pos _).le (mul_nonneg he r))).trans_eq (by unfold M L' gleam Y; ring))
end YM.CF.Wray
