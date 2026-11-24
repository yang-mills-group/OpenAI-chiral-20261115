import YM.SU5.FiniteGaugeData.Nine.Brisee
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Chaperone Heat Afterglow.Hierarchy.Eight Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
open Window.Pivot
variable (o:Cover) {N:Side}
local notation "Μ"=> Single N
open Fock Fock.Brique
local notation "H₀"=> (polarQ o)
open Nacre
lemma rayFine {b:Bool}{T:Support (More N)} (v: Earn o T){A:FC (Single N)} (p:Fine (Tset N) (modesIn N T) b A): Fine (Tset N) (modesIn N T) b (imageQ (polarQ o) N A):=by
 let U:= Window.Pivot.Port o N; let S:=modesIn N T; let s:=Tset N; have he:=moves_H o N; let B:=quantU U
 have hu:twist U (cutM S)=cutM S:= (moves_W o N T).trans (congrArg (fun i=> cutM (modesIn N i)) v.symm);
 have ht:twist U (cutM sᶜ)=cutM sᶜ:=by rw [dim_cut,map_sub,map_one,show twist U (cutM s)= _ from he]
 have hv(R:Finset Μ)(i)(v:twist U (cutM R)= cutM R)(u:i∈R):withinM R (acts U.val (basisKet i)):=by unfold withinM; nth_rw 1 [←v]; rw [← Fock.swivel, within_basis R i u]
 change Fine _ _ b (twist (quantU _) A);
 induction p with
 | seed i p=> by_cases t:i∈ Tset N
              · rw [show (Reed.think (Tset N)).term i=put i from if_pos t,←create_put,twist_create]; exact fine_create _ (hv _ i he t) (hv _ i hu p)
              rw [show (Reed.think (Tset N)).term i= -takeF i from if_neg t,map_neg,←remove_take,twist_remove]; exact fine_neg (fine_remove _ (hv _ i ht (mem_compl.mpr t)) (hv _ i hu p))
 | empty=>rw [map_zero]; exact .empty _
 | one=> rw [imageOne]; exact .one
 | add _ _ a b=>rw [map_add]; exact a.add b
 | grow _ _ a b=>rw [map_mul]; exact a.grow b
 | scale _ _ a=>rw [twist_scalar]; exact a.scale _
lemma cargoCL {T R:Support (More N)}{W : Pane N→ℂ}{o:Seat N} (F:Corset T R o): ∃ p:FC (Single N)→ₗ[ℂ] Mark N, ∀ x,p x=cargo F W x:=by
 let v:FC (Single N)→ₗ[ℂ] Mark N:= {
 toFun:=cargo F W
 map_add' x y:= funext fun i=> (congrArg (fun a: FC Μ=> W i.1 • a) (map_add (Window.Brique.flipsP _ ) x y)).trans (smul_add ..) -- tune native flipsP is AlgEquiv
 map_smul' z x:= by funext i; unfold cargo; rw [flipsP,twist_scalar]; exact smul_comm .. }
 exact ⟨v,fun _=>rfl⟩
abbrev loadF {T R: Support (More N)}{o:Seat N}(F:Corset T R o)(W :Pane N→ℂ) := Classical.choose (cargoCL (W:=W) F) -- using alc choice.These commute with multiplication partial.NonDet; actual
lemma load_exact{T R:Support (More N)}{W:Pane N→ℂ}{o:Seat N}(F:Corset T R o)(x:FC (Single N)): loadF F W x=cargo F W x:= Classical.choose_spec (cargoCL F) _
lemma cent_ray (H: Shape) (x:FC (Single N)) : imageQ H N (centB N x)=centB N (imageQ H N x):=by
 let L:FC (Single N)→L[ℝ] FC Μ:=⟨(twist (quantU (prepU H 1 inert N))).toAlgEquiv.toLinearMap, Fock.breeze _⟩; let Φ:= SU.group.probHaar
 change L (∫ i:SU.E, orbitB x i ∂Φ)=∫ i:SU.E, orbitB (L x) i ∂Φ; rw [← ContinuousLinearMap.integral_comp_comm L (orbit_integrable _)]; exact integral_congr_ae (Eventually.of_forall fun i=> (pollen N H (globalH N i) x)) -- pollen order
section funds
variable {T R U:Support (More N)}{Q:Finset (Site N)}{W:Pane N→ℂ}{C C' c d γ t ε:ℝ}{n w k:ℕ}{K:Loom N} {Z: Peg N}
variable (F:Corset T R (wrap (More N) o))(L:Mark N→ₗ[ℂ] ℂ)(sR:Earn o R)(sT:Earn o T)
variable (O:Casing N Z.e (Z.Ft false) c C d) (I:0≤ C)
local notation "P"=>Z.Ft false
local notation "Y"=> (sapW o W)
local notation "Σ"=> cargo F (sapW o W)
local notation "t₀"=> tailCost c C w
local notation "B₁"=> (frameP o F sR sT)
variable (γ0: γ +(2*tailCost c C w+t*C) ≤ ε-tailCost c C w)
variable (Gu:Earn o U)(v:CashMask F W U (d*t) K)(u:U⊆R)(H:Lattice.halo w T⊆ U)
structure Pay (L:Mark N→ₗ[ℂ]ℂ) (n w:ℕ)(C':ℝ)(c C ε:ℝ)(Z:Peg N)(R:Support (More N))(K:Loom N) : Prop where
 tends: ∀ f g:Mark N, AtSupport false R f→ AtSupport false R g→ (∀ x, ‖f x‖ ≤ C') → (∀ x,‖g x‖≤ C')→(∀ x:Orbit N, g (drawn K x)=f (drawn K x)) → Crater w (tailCost c C w) ε Z R g n false → ‖L f‖ ≤ (1/8:ℝ)
variable (q:Pay L n w C' c C ε Z R K)(G:0≤ Z.e)
include O G I γ0 q u H
private lemma caredPay (F:Corset T R (wrap (More N) o))(h:CashMask F W U (d*t) K) (x:FC (Single N))(p:Mirage.Marble (Z.Ft false 1) T n x γ)(tF:Fine (Tset N) (modesIn N T) false x)(hp:‖x‖ ≤ C') : ‖L (cargo F W x)‖ ≤ 1/8:=by
 have ht:T⊆R:= Subset.trans (Subset.trans (halo_subset ..) H) u; let he:= delivered F h.faces ht tF; let X:= cargo F W x; have hv(z):‖X z‖ ≤ C':= (cargo_bound F h.faces x z).trans hp
 apply q.tends X (cared U X) he.zone (cared_area X he u) hv (fun z=> (cared_cost X U z).trans (hv z)) (stampEq h x) (Mirage.paid_copy O h p H G (mul_nonneg (Real.exp_pos _).le I) γ0 u)
private lemma centPay (F:Corset T R (wrap (More N) o))(h:CashMask F W U (d*t) K)(x:FC (Single N)) (p:Mirage.Marble (Z.Ft false 1) T n x γ)(tF:Fine (Tset N) (modesIn N T) false x)(hp:‖x‖ ≤ C') : ‖L (cargo F W (centB N x))‖ ≤ 1/8 :=by
 let A:= lobby L W F; let Φ:=SU.group.probHaar
 change ‖A (∫ i,orbitB x i ∂Φ)‖ ≤_; rw [←ContinuousLinearMap.integral_comp_comm A (orbit_integrable ..)]; refine (norm_integral_le_of_norm_le (integrable_const (1/8)) (Eventually.of_forall fun i=>?_)).trans (by simp [Φ]) -- type
 let g:=globalH N i; have hP: ‖orbitB x i‖ ≤ C':= (twist_norm ..).le.trans hp; apply caredPay o L O I γ0 u H q G F h (orbitB x i) ?_ (windFine g tF) hP
 have he:= p.turned g; rw [← Casing.coloredWT O _ (guard0 G),globalWind] at he; exact he -- tune
include v sR sT Gu H
variable {x:FC (Single N)}(tF:Fine (Tset N) (modesIn N T) false x)(pF:‖x‖ ≤ C')
include tF pF
lemma dualCost : ( Mirage.Marble (Z.Ft false 1) T n x γ → ‖L (cargo F Y (centB N x))‖ ≤1/8) ∧ (Mirage.Marble (piQu o N (Z.Ft false 1)) T n x γ → ‖L (pageF o N (cargo F Y (centB N x)))‖≤1/8) :=by
 let he:= cutBoth o F sR sT Gu v; refine ⟨fun p=> centPay o L O I γ0 u H q G F he.1 x p tF pF,fun p=>?_⟩
 rw [sky_cargo o F sR sT, cent_ray,sky_identity]; obtain h':= marble_image o N γ p; rw [sT.symm] at h'; refine centPay o L O I γ0 u H q G (frameP o F sR sT) he.2 _ ((glue0 o (Z.Ft false 1)) ▸ h') (rayFine o sT tF) ((twist_norm ..).le.trans pF) -- tune ▸ notation glue0
end funds
#print axioms cent_ray
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Chaperone Heat Afterglow.Hierarchy.Eight Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
open Window.Pivot
variable (o:Cover) {N:Side}
local notation "Μ"=> Single N
open Fock Fock.Brique
local notation "H₀"=> (polarQ o)
open Nacre
variable {Λ:Preparation}(k m n w:ℕ)(σ:Window.Family) (Q:Finset (Site N))(T: Support (More N))(M: Male) -- o argument order for focusCost at funds
local notation "g"=> bossColor σ
local notation "C₁"=>tableI Q.card
local notation "Α"=> σFee
local notation "Q₁"=> volts (bossColor σ) Q
local notation "F" U:max => officeH o k M (bossColor σ) Q T U
local notation "γ_" c:max=> opt c*(σFee/2)⁻¹
section
variable (x:1≤k) (e:Aptitude k N) (h:‖(emU k M (bossColor σ) Q)‖ ≤ 1-σFee/2) (q: Lattice.halo (2*w) (Q.image node)⊆ T)(U:Finset (Single N))
local notation "P" => funde k M N 1
variable {c:ℝ}(C: Liquid w (funde k M N 1) c)
include h
lemma satisfy :IsUnit (1-emU k M (bossColor σ) Q):= isUnit_one_sub_of_norm_lt_one (lt_of_le_of_lt h (by linarith [σFee_pos]))
include x e
lemma ampleCost : ‖F U‖ ≤ C₁:= by
 refine (pay_norm o k M (bossColor σ) Q T U x e (satisfy k σ Q M h) (half_pos σFee_pos) h).trans (Eq.le ?_)
 rw [←bossPopulation,knob_size]; rfl
include q
lemma yearning : Barque σ Q (T\ Q.image node) (F U-1):= office_shape o k M (bossColor σ) Q σ T U x e (satisfy k σ Q M h) ((halo_subset ..).trans q) rfl
-- tune structure
include C q
#check Finset.exists_subset_card_eq
lemma pace_cost (u:U ∈ ((Q₁).powerset))(p: 2*n= Q.card) : (n ≤ U.card → Mirage.Marble (funde k M N 1) T n (F U) (γ_ c)) ∧ (¬ n ≤ U.card→ Mirage.Marble (piQu o N P) T n (F U) (γ_ c)):=by
 have he : (Q₁).card= Q.card:= by rw [←bossPopulation]; exact knob_size ..
 -- ; -- remove
 have hz : U⊆ Q₁:= mem_powerset.mp u;
 let A (S:Finset Μ)(t:S⊆ Q₁):= pay_choice o k M (bossColor σ) Q T U S x e (satisfy k σ Q M h) (half_pos σFee_pos) h C q t
 constructor <;> intro h
 · obtain ⟨S,v',rfl⟩:=Finset.exists_subset_card_eq h; exact (A S (v'.trans hz)).1 v'
 have ht: n ≤ ((Q₁) \ U).card:= (by rw [card_sdiff_of_subset hz,he]; omega)
 obtain ⟨S,t,rfl⟩:= exists_subset_card_eq ht; exact (A S (t.trans sdiff_subset)).2 (disjoint_left.mpr fun i w u=> (mem_sdiff.mp (t u)).2 w)
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
