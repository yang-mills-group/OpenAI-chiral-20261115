import YM.SU5.FiniteGaugeData.Galope.Silent
import YM.SU5.FiniteGaugeData.Lapis.Cloche
/-! # Frame. Ambient tangent Gaussian and projection prices for growth occupancy.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
set_option quotPrecheck false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Lapis
open Function Finset Filter MeasureTheory ProbabilityTheory Matrix Lattice Wilson RG Precision Tree Next.Fluctuations Work.F03
open Pressure Exterior Laurent Bloch Drachma Galope Avenue Galope.Press Wrist Poeme Haute Punch
open scoped Topology InnerProductSpace Matrix MatrixOrder RealInnerProductSpace ContDiff BigOperators NNReal ENNReal Kronecker Classical
namespace Affiche
open Next.Rank.Axial
variable {n: Side}{G: Gauge}{Z: Finset (Site n)} {K w k:ℕ} {C r β a Δ:ℝ} {P:Bed}{u:Stage}{R:PathData G} {Q H:Finset (Bond n)}
-- centers without orientations. includes harmonic regulator even at this preparation, and trunk bits.Fixed.M.
abbrev denim(n:Side) := (axle n).trunksᶜ
def zodiac (P:Bed)(G:Gauge) (Q:Finset (Bond n)) : sp (Plush G Q):= ((chips (axle n) P).submatrix (tabKey Q) (tabKey Q))⊗ₖ (1:sp G.ColorIndex)
lemma shine(Q:Finset (Bond n))(G:Gauge)(h:Floor P u.clip n a C)(v:0<a): (zodiac P G Q).PosDef := ((chips_live (axle n) h v).submatrix (tab_in Q)).kronecker PosDef.one
lemma brushing(Q:Finset (Bond n))(W: R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(D:Floor P u.clip n a C) (g:coin (Plush G Q)) : ‖heatC univ W A (kickC Q g)‖^2 ≤ dotProduct g (zodiac P G Q*ᵥ g):=by
 rw [attainedE,wholeC D W A, zodiac, chrome_eraP]; apply sum_le_sum; intro i _; rw [costsA]; let x:= KickC Q g i
 change dotProduct x (plaid P n *ᵥ x) ≤ dotProduct x (chips (axle n) P *ᵥ x)
 unfold chips; rw [plus_bill,plus_bill]; linarith only [prize_nn (tickets (axle n)) x, prize_nn (lasers n) x]
-- omission.Inclusion
abbrev flex (h:Q⊆H) (i:Plush G Q): Plush G H:= (⟨i.1.val,h i.1.property⟩,i.2)
lemma omni(h:Q⊆H): Injective (flex (G:=G) h) := fun x y t=> Prod.ext (Subtype.ext (congrArg (fun x:Plush G H=>x.1.val) t)) (congrArg (fun x:Plush G H=>x.2) t)
abbrev lobby (G:Gauge)(h:Q⊆H): coin (Plush G Q)→ₗ[ℝ] coin (Plush G H):= (foot (flex (G:=G) h)).mulVecLin
lemma in_amber (h:Q⊆ H)(x:coin (Plush G Q)): kickC H ((lobby G h) x)=kickC Q x:=by
 ext i z; obtain ⟨i,rfl⟩:= (portfolio n).surjective i; change kickC H _ (markZ n i) z=kickC _ _ _ z; by_cases q:i∈Q
 · have ht:=at_tab x (⟨i,q⟩:↥Q); have hz:=at_tab (lobby G h x) (⟨i,h q⟩:↥H); change kickC H _ (markZ n (↑(⟨i,h q⟩:↥H))) z=kickC Q _ (markZ n (↑(⟨i,q⟩:↥Q))) z; rw [ht,hz]; exact hold (flex h) (omni _) _ ((⟨i,q⟩:↥Q),z)
 rw [at_key x i q]; by_cases u:i∈ H; swap; · rw [at_key _ _ u]
 let l:↥H:=⟨i,u⟩; let z':=(l,z); change kickC _ _ (markZ n l.val) z=(0:G.Color) z; rw [at_tab]; apply blankA (flex h); rintro ⟨k,v⟩; exact q (by have ht:k.1.val=i:=congrArg (fun y:Plush G H=> y.1.val) v; exact ht ▸ k.1.property) -- tune
lemma placate (P:Bed)(h:Q⊆H)(x:coin (Plush G Q)) : dotProduct (lobby G h x) (zodiac P G H*ᵥ (lobby G h x)) = dotProduct x (zodiac P G Q *ᵥ x):= by
 have ht :(zodiac P G H).submatrix (flex h) (flex h)= zodiac P G Q:= rfl; rw [←ht,costsA]; rfl
-- evaluator R with scale µ. Emits Portion.Note reference F depends only on direct rows. 
variable (Q)
def castM (W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(D:Floor P u.clip n a C)(hp:0<a) : Vault (Plush G Q) →ₗ[ℝ] Portion n G := (heatC univ W A).comp ((keyM G Q).comp (bridgeB (zodiac P G Q) (shine Q G D hp)).toLinearMap)
lemma glance (W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(D:Floor P u.clip n a C)(hp:0<a) (x:Vault (Plush G Q)) : ‖castM Q W A D hp x‖ ≤ ‖x‖:= by
 let h:= shine Q G D hp; let v:= bridgeB (zodiac P G Q) h x; apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1; change ‖heatC univ W A (kickC Q v)‖^2 ≤ _; exact (brushing Q W A D v).trans_eq (chalk _ h x)
lemma bye(h:Q⊆H)(D:Floor P u.clip n a C)(hp:0<a)(hz:0<r)(G:Gauge)(x:coin (Plush G Q)): let S:= zodiac P G Q; let L:=Real.sqrt r • lobby G h; dotProduct (L x) (zodiac P G H*ᵥ (L x))=dotProduct x ((r•S)*ᵥ x):=by
 intro S L; let V:=zodiac P G H; let v:=lobby G h x; change dotProduct (Real.sqrt r • v) (V*ᵥ (Real.sqrt r • v))=_; rw [mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul,smul_eq_mul,← mul_assoc,← pow_two,Real.sq_sqrt hz.le,show dotProduct v (V*ᵥv)=_ from placate P h x,smul_mulVec,dotProduct_smul,smul_eq_mul] -- tune
-- embedding Stamina responds to SP rescaling.
variable {Q}
include P
abbrev inlet (h:Q⊆H)(D:Floor P u.clip n a C)(hp:0<a)(hz:0<r)(G:Gauge) := venue (zodiac P G H) (r•zodiac P G Q) (shine H G D hp) ((shine Q G D hp).smul hz) (Real.sqrt r • lobby G h) (bye Q h D hp hz G)
lemma liftZ (h:Q⊆H)(W:R.Bounds u.clip u.width u.paths Δ)(A:Attached P R)(D:Floor P u.clip n a C)(hp:0<a)(hz:0<r)(x:Vault (Plush G Q)): castM H W A D hp (inlet h D hp hz G x)=Real.sqrt r • heatC univ W A (kickC Q (bridgeB (r•zodiac P G Q) ((shine Q G D hp).smul hz) x)):=by
 let b:=bridgeB (r•zodiac P G Q) ((shine Q G D hp).smul hz); let T:= heatC (n:=n) univ W A
 change T (keyM G H (bridgeB _ (shine H G D hp) (inlet h D hp hz G x))) = Real.sqrt r • T (keyM G Q (b x)) -- tune
 rw [inlet,valued,LinearMap.smul_apply,map_smul,map_smul]; exact congrArg (fun v:LogField G n=> Real.sqrt r • T v) (in_amber h _)
end Affiche
end YM.SU5.FiniteGaugeData.Lapis
#print axioms YM.SU5.FiniteGaugeData.Lapis.Affiche.liftZ
