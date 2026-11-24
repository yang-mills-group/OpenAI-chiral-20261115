import YM.CF.BProof.Push.Dark
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau.PushA
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Iva Lilt Salt Palot Floral Sour Haro Tap Sour.BondL Mew
open scoped YM.CF.Mew
variable {ε γ R Q κ Z:ℝ}{C V D A:Cusp n}
abbrev cashLine (C D:Cusp n)(v:ℂ) := C+v • (D-C)
private lemma flash{D:Support (More n)}{x:Aura n}(v:ℂ)(p:Vow.Firm P x.val D (C x D))(u:Vow.Firm P x.val D (V x D)) : Vow.Firm P x.val D ((cashLine C V v) x D):=by
 refine ⟨fun h=>?_,fun i h=>?_⟩; · change C x D+v • (V x D-C x D)=_; rw [p.readV h,u.readV h]; simp
 by_contra t; refine h ?_; change C x D i+v • (V x D i-C x D i)=_; rw [of_not_not (mt (p.litK i) t), of_not_not (mt (u.litK i) t)]; simp
structure Case (P:BudgetPoint)(h γ Z Q ε:ℝ)(C V D A:Cusp n):Prop where
 small:0<ε
 big:ε≤1
 zero:Wheel P h γ Z Q C V
 e:Binder P h (kδ P+wΨ) (lightP (D-C)) (3*ε*γ)
 q:Flaws P h (kδ P+wΨ) (D-C) (3*ε*Z)
 t:Heats P h (kδ P) (A-V) (ε*Q)
 ok: bolt P D
variable {z:ℂ}
namespace Case
variable (t:Case P h γ Z Q ε C V D A) (p:Crowd P h (8*γ) (8*Z) (4*Q) R κ)
include p t
lemma born(u:z∈disk (1+1/ε)): Wheel P h (8*γ) (8*Z) (4*Q) (cashLine C D z) (cashLine V A z):=by
 have hx:0≤ kδ P:=add_nonneg (add_nonneg P.exponent_pos.le zero_le_one) zero_le_one; have he:0≤kδ P+wΨ:=add_nonneg hx (show 0≤wΨ from by norm_num [wΨ]); have h0:=zero_le_one.trans p.zH
 have hp: ‖z‖ ≤1+1/ε:= by rw [disk,mem_ball_zero_iff] at u; exact u.le
 have l(v:ℝ)(h:0≤v)(a:ℝ)(g:0≤a): v+ ‖z‖*(a*ε*v)≤(1+2*a)*v:=by
    have hu:=t.small; calc
     _ ≤ v+(1+1/ε)*(a*ε*v):=by gcongr
     _ = v+ε*(a*v)+a*v:=by field_simp; ring
     _ ≤ _ := by apply le_trans (add_le_add_left (add_le_add_right (mul_le_of_le_one_left (mul_nonneg g h) t.big) v) (a*v)); exact le_of_eq (by ring)
 refine ⟨Wallet.mono (Binder.plus t.zero.e (Binder.σ t.e z)) ?_,Wallet.mono (Flaws.plus t.zero.q (Flaws.σ t.q z)) ?_,Wallet.mono (Heats.plus t.zero.t (Heats.σ t.t z)) ?_,fun i D h v=> flash z (t.zero.ok i D h v) (t.ok i D h v)⟩ -- need light definitional
 · have hu:=Binder.pos t.zero.e he h0; exact (l _ hu _ (show 0≤(3:ℝ) by norm_num)).trans (by gcongr; norm_num)
 · have h':=Flaws.pos t.zero.q h0 he; exact (l _ h' _ (show 0≤(3:ℝ) by norm_num)).trans (by gcongr; norm_num)
 have hv:=Heats.pos t.zero.t hx; have hy:=l _ hv 1 zero_le_one; rw [one_mul] at hy; exact hy.trans (by gcongr; norm_num)
lemma lips : Pressed P (burn P D A-burn P C V) h (ε*Cog_P P R κ):=by
 have l:1<1+1/ε:= lt_add_of_pos_right _ (div_pos zero_lt_one t.small)
 have hv(C V:Cusp n)(i:Aura n)(x:Orbit n)(D:Support (More n)): Hol (disk (1+1/ε)) (fun z=> cashLine C V z i D x) := by change Hol _ (fun z=>C i D x+z • (V i D x-C i D x)); exact (differentiableOn_const (C i D x)).add ((differentiableOn_id (𝕜:=ℂ) (s:=disk (1+1/ε))).smul (differentiableOn_const (V i D x - C i D x)))
 have hx:= LipsK_line p l (fun z u=> t.born p u) (hv C D) (hv V A); have hp(z v:Cusp n): cashLine z v 1=v:=by unfold cashLine; rw [one_smul]; abel
 rw [hp,hp, show cashLine C D 0=C from (by simp [cashLine]), show cashLine V A 0=V from (by simp [cashLine]), add_sub_cancel_left,div_div_eq_mul_div,div_one,mul_comm] at hx -- mul_comm danger.
 exact hx
end Case
end YM.CF.Beau.PushA
