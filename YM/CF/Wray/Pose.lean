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
open Iva Eire Font
local notation "Z_"=> Domain N B
local notation "c'"=> Single N
local notation "Φ"=> Branch.ledgerV
-- COLOR set occupancy(real). No unproven host exceptions
abbrev countH(r:ℕ):= (r+r+1)^4*Fintype.card (SpinIdx×SU.Slot)
lemma lens_u(o:Site (More N))(r:ℕ){U:ℝ}(h:0≤U): Branch.ledgerV (groveR N r o U) ≤ (countH r:ℝ)^2 * U:=by
 let X:=halo r {o}; let b(i:c'): Prop:= place_x i∈ X; let A:= univ.filter fun i:c'=> b i
 have hh: Injective (@node N):= fun x y h=> (assembly N).embed_injective (add_right_cancel (show _+(1:Site (More N))=_+_ from h))
 let p(i:c'):= (node i.1.1,i.1.2,i.2); have hx:A.card ≤ countH r:=by
    have ht:Injective p:=by rintro ⟨⟨u,v⟩,w⟩ ⟨⟨f,g⟩,h⟩ z; unfold p at z; simp only [Prod.mk.injEq] at z; simp [z,hh z.1]
    apply le_trans (b:=(X ×ˢ (univ: Finset (SpinIdx× SU.Slot))).card) ?_ (by rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ ((Corona.halo_size {o} r).trans (by simp)))
    rw [← card_image_of_injective _ ht]; apply card_le_card; exact image_subset_iff.mpr fun i h=> mem_product.mpr ⟨((mem_filter.mp h).2),mem_univ _⟩
 let Y:= groveR N r o U; calc
   Φ Y=∑ i∈A,∑ j∈A,U:=by
      unfold Branch.ledgerV; rw [←sum_subset (subset_univ A)]; swap; · intro i _ k; apply sum_eq_zero; intro j _; exact if_neg (fun x=> k (mem_filter.mpr ⟨mem_univ _,x.1⟩))
      apply sum_congr rfl; intro i z; rw [←sum_subset (subset_univ A)]; swap; · intro j _ k; exact if_neg (fun x=> k (mem_filter.mpr ⟨mem_univ _,x.2⟩))
      exact sum_congr rfl fun j v=>if_pos ⟨(mem_filter.mp z).2,(mem_filter.mp v).2⟩
   _ ≤ _:=by rw [sum_const,sum_const]; simp only [nsmul_eq_mul, ←mul_assoc,← sq]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg A.card) (Nat.cast_le.mpr hx) 2) h
open Pail
variable {σ x0':ℝ} {F:Pilot}{Z:Pluck R}
local notation "L_"=> (radiusB x)
abbrev bonusH(a v p H:ℝ)(k:ℕ)(x:ℝ):= steel k (Kplan k a+v)+ H^2* steel k ((countH (radiusB x+1):ℝ)^2*Kplan k p)
lemma primA(o:Site (More N))(W:Wages)(T:ℝ)(u:0 ≤ W.tip)(v:0 ≤ W.ego)(x_:0≤W.puff)(ht:0 ≤ T): let B:= bonusH W.tip W.ego W.puff T k x; 0 ≤ B ∧ joinV (stake T) (bronze (N:=N) x o W k) ≤ Real.exp B * B:=by
 let D:= (bronze (N:=N) x o W k); let Y:= Iva.cull k (statue (N:=N) x o W k) (Kplan k W.tip+W.ego); let P':= joinV (stake T) Y; have hx:0 ≤ Y:= cull_p _ _ (fun i j=>gro_p _ (plan_nn k x_) _ _ _ _) (add_nonneg (plan_nn k u) v)
 intro B; have ht':P' ≤ B:=by
    unfold P' Y; rw [stars]; unfold B bonusH; refine add_le_add (le_refl _) (?_); -- tune
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lens_u o (L_+1) (plan_nn k x_)) (by positivity)) (sq_nonneg T)
 have hZ:0 ≤ P':= sum_nonneg (fun i _=> mul_nonneg ((stokes ht).fee i) (hx i)); refine ⟨hZ.trans ht',?_⟩; apply (Rue.peony 1 hx (stokes ht)).trans; rw [pow_one]; exact mul_le_mul (Real.exp_monotone ht') ht' hZ (Real.exp_pos _).le
variable{A' : Stake.Isle}{Q:Tun A' Z F σ}
abbrev sapX{E:Stake.Isle} (Q:Tun E Z F σ)(T:ℝ)(k:ℕ)(x:ℝ):=let p:=paidL E Q.K₁ Q.K₂ k x (F.hat R x); bonusH p.tip p.ego p.puff T k x
lemma boring : BoreP (fun x=>(countH (radiusB x+1):ℝ)):=by unfold countH; push_cast; let h:= BoreP.radius_c.join (BoreP.still 1); exact ((((h.join h).join (BoreP.still _)).self _).grip (BoreP.still _))
lemma bonuses(H:ℝ) : sizeK R.L 1 (sapX Q H k):=by
 let p:=tall_a A' Q.K₁ Q.K₂ k; unfold sapX bonusH steel; dsimp only; exact ((((rates.arm _ _ _ p.tip).accrue p.ego).scale _).accrue (((((boring.self 2).creditK R.L).tint (rates.arm _ _ _ p.puff)).scale _).scale _))
-- halo-single.
lemma rigger{U:Muster G S x d T}(X:Site (Domain N B))(k':ℕ)(t:0<radiusB x): (vast (k:=k'*L_) U (.inr (.inl X))).val⊆ halo ((k'+24)*L_) {X}:=by
 intro z p; change z∈ halo 20 (halo 1 (halo (k'*L_+2) {X})) at p; obtain ⟨i,v,u⟩:= halo_spec.mp p; obtain ⟨j,g,h⟩:= halo_spec.mp v; obtain ⟨a,p,v⟩:= halo_spec.mp g; apply halo_spec.mpr; refine ⟨a,p,(separation_triangle a j z).trans ?_⟩; have ht:= separation_triangle j i z; rw [Nat.add_mul]; omega
abbrev friday(H a:ℝ)(z x:ℝ)(s:ℕ):= Real.exp (a*((s+s+49:ℕ)^4:ℕ))* Real.exp 1 * z -- H x phantom
lemma prima (H:ℝ)(a:ℝ)(Z:Muster G S x d T)(o:Site (Domain N B))(h:0 ≤ a) (p:0 < radiusB x)(w:0 ≤ H)(e:sapX Q H k x ≤ 1)(f:ℕ) : Trees.currency (radiusB x) a (vast (k:=f*radiusB x) Z (.inr (.inl o))).val * joinV (stake H) (bronze (N:=mid N B) x o (paidL A' Q.K₁ Q.K₂ k x (F.hat R x)) k) ≤ friday H a (sapX Q H k x) x f:=by
 let W':=sapX Q H k x; obtain ⟨hp,H'⟩:= primA (x:=x) (k:=k) o (paidL A' Q.K₁ Q.K₂ k x (F.hat R x)) H (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) w
 let P':= (vast (k:=f*L_) Z (.inr (.inl o))).val; have ht:coverNumber L_ P'≤ (f+f+49)^4:=((Corona.cover_mono (rigger o _ p) L_).trans (Corona.tile o _ _ p)).trans (by ring_nf; exact le_rfl)
 let C:= Trees.currency L_ a P'; let y:= Real.exp (a*((f+f+49:ℕ)^4:ℕ)); have hx:C ≤ y:= Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ht) h); apply (mul_le_mul_of_nonneg_left H' (show 0 ≤ C from (Real.exp_pos _).le)).trans; exact ((mul_le_mul hx (mul_le_mul_of_nonneg_right (Real.exp_monotone e) hp) (mul_nonneg (Real.exp_pos _).le hp) (Real.exp_pos _).le)).trans_eq (by unfold friday; exact (mul_assoc y _ W').symm)
end YM.CF.Wray
