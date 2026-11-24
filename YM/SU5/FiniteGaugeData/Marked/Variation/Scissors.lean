import YM.SU5.FiniteGaugeData.Marked.Variation.Ribbon

/-! # One-step Menu for a fixed CAR letter on variable tori -/
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Fock Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye
attribute [local instance] opCStarAlgebra
variable {X I : Type*} [MeasurableSpace X](N: I→ Side)
variable (v:I→ X→SU.E)(n:∀i, X→ Pane (N i))(p:∀ a:(i:I)→ Edge (Site (More (N i))), Deal (fun i x=> n i x (a i): I→X→SU.E))
private lemma esquare(k w: I→ X→SU.E)(p:Deal k)(a:Deal w):Deal (fun i x=> k i x*w i x:I→X→SU.E):=(p.prod a).post (continuous_fst.mul continuous_snd)
private lemma eturn(k: I→ X→SU.E)(p:Deal k):Deal (fun i x=> (k i x)⁻¹:I→X→SU.E):=p.post continuous_inv
include p
lemma roam (w:Walk):∀ a:(i:I)→Seat (N i), Deal (fun i x=> Lattice.travel (n i x) (a i) w:I→X→ SU.E):=by
 induction w with
 | nil=> exact fun a=> Deal.pure (fun _:I=> (1:SU.E))
 | cons s w ih=>
   intro a; let b(i):=s.used (a i)
   have h:=p b
   cases u:s.neg
   · simpa only [travel,Step.read,u, Bool.false_eq_true, ↓reduceIte] using esquare _ _ h (ih fun i=> a i+s.vec)
   simpa only [travel,Step.read,u,↓reduceIte] using esquare _ _ (eturn _ h) (ih fun i=> a i+s.vec)

section
variable (L:Side)(P:I→Side)(sz:∀ i,(P i).val=(N i).val*L.val)
abbrev bead (i:I):Ratio (N i) (P i):= ⟨L,sz i⟩
end
variable (L:Side)(P:I→Side)(sz:∀ i,(P i).val=(N i).val*L.val)
local notation "G" => bead N L P sz
local notation "StateT" => St L
variable (j D:ℕ)(vA:LaurentRadius j L D)(k:(i:I)→Iota (bead N L P sz i)) (w:(i:I)→ X→Nom (N i) (P i))(pay:∀ a:(i:I)→ Edge (Site (More (P i))), Deal (fun i x=> (w i x).1 (a i): I→ X→SU.E))
omit p

include pay
lemma silks (z:Cover)(r:StateT)(f:SU.Slot)(o:Lattice.Order): Menu (fun i u=>fall (G i) j (k i) z r f o (w i u):I→X→ℂ):=by
 let Z(i:I):Seat (P i):= Peaks.touch (G i) true ((k i).1.1-wrap (N i) z,r)
 let U(h:St L)(i:I)(u:X):SU.E:= travel (w i u).1 (Z i) (runD true false L r h z o)
 have hu(h): Deal (U h):= roam P _ pay _ Z
 let y(i:I):= (k i).2
 let t(i:I):St L:= (k i).1.2
 have hU:Deal (fun (i:I)(x:X)=> U (t i) i x):= Deal.assembly U hu t
 let m(h:SU.Slot)(i:I)(x:X):ℂ:= (SU.matter (U (t i) i x)).val f h
 have ht(h):Menu (m h):= Menu.post hU (show Continuous (fun x=> (SU.matter x).val f h) from SU.matter_cont.matrix_elem ..)
 have rM:Menu (fun (i:I)(x:X)=> m (y i) i x):=by
    refine ⟨Deal.assembly m (fun j=> (ht j).deal) y,1,zero_le_one,fun i x=>(norm_entry ((SU.matter (U (t i) i x)).val) f (y i)).trans (CStarRing.norm_of_mem_unitary (SU.matter _).property).le⟩
 obtain ⟨c,h⟩:= (Set.finite_range (fun t:St L=> ‖tub (brix j L) z r t‖)).bddAbove
 let ρ(i:I):= Rush.wind ((k i).1.1-wrap (N i) z) z * (tub (brix j L) z r (t i))
 have he (i:I): ‖ρ i‖ ≤ max c 0:=by unfold ρ; rw [norm_mul,Rush.wind,Rush.fee_norm,one_mul]; exact (h ⟨_,rfl⟩).trans (le_max_left ..)
 exact (Menu.cnst ρ (le_max_right _ _) he).mul rM

omit pay
private lemma warp (b:Bool)(i l:(i:I)→Iota (bead N L P sz i)): Menu (I:=I) (X:=X) (T:=fun _=>ℂ) (fun a _=> lobe (G a) b (i a) (l a)):= Menu.cnst _ zero_le_one (fun v=>(norm_entry (lobe (G v) b) (i v) (l v)).trans (IsStarProjection.norm_le _ (lobe_sq ..)))
private lemma tex(k:(i:I)→Iota (bead N L P sz i)): Menu (T:=fun i=>Ket (Iota (bead N L P sz i))) (X:=X) (fun i _=> basisKet (k i)):=Menu.cnst _ zero_le_one (by simp [basisKet])
include pay
private lemma silk_term (b:Bool)(p':St L)(z:Cover)(f:SU.Slot)(o:Lattice.Order):
 let u:= fun i=> pick (G i) (k i) z p' f
 Menu (T:=fun i=> Ket (Iota (bead N L P sz i))) (fun (i:I)(x:X)=>
   (lobe (G i) b (u i) (u i)* fall (G i) j (k i) z p' f o (w i x) * lobe (G i) b (k i) (k i)) • basisKet (u i)):=by
 intro u
 exact (((warp N L P sz b u u).mul (silks N L P sz j k w pay z p' f o)).mul (warp N L P sz b k k)).scale (tex N L P sz u)
lemma silk_half (b: Bool):Menu (T:=fun i=> Ket (Iota (bead N L P sz i))) (fun (i:I)(x:X)=>half (G i) j (R:=D) (k i) b (w i x)):=by
 unfold half
 refine (Menu.cnst (fun _:I=> (Fintype.card Lattice.Order:ℝ)⁻¹) (norm_nonneg _) (fun _=> le_rfl)).scale ?_
 apply Menu.total (T:=fun i=> Ket (Iota (bead N L P sz i))) (univ:Finset Lattice.Order) (fun o i x=> ∑ r:St L,∑ z∈ LabelSet D,∑ f:SU.Slot,(let u:= pick (bead N L P sz i) (k i) z r f; lobe (G i) b u u * fall (G i) j (k i) z r f o (w i x) * lobe (G i) b (k i) (k i)) • basisKet (pick (G i) (k i) z r f))
 intro o _
 refine Menu.total (univ:Finset (St L)) _ ?_; intro p' _
 refine Menu.total (LabelSet D) _ ?_; intro z _
 refine Menu.total (univ:Finset SU.Slot) _ ?_; intro f _
 exact silk_term N L P sz j k w pay b p' z f o
include vA
section
variable (M : I→Male) (Q: I→Op SU.Slot) {d:ℝ} (y:∀i,‖Q i‖ ≤ d)
include y
private lemma linen (b:Bool)(v:(i:I)→Single (N i)): Menu (T:=fun i=>Ket (Iota (bead N L P sz i)))
   (fun (i:I)(x:X)=> acts (Peaks.cloth j (M i) (G i) (Peaks.unionP (w i x))) (coat (patchQ (G i)) (acts (feeL b (N i) (Q i)) (basisKet (v i))))):=by
 let x₀(i:I):= (v i).1.1; let x₁(i:I):spinSlot:= ((v i).1.2,(v i).2)
 let J(i:I)(c:spinSlot):= patchQ (G i) (nick (N i) (x₀ i) c)
 obtain ⟨L',n,e⟩:= room_bound d
 have m(c:spinSlot):Menu (I:=I) (X:=X) (T:=fun _=>ℂ) (fun a _=>roomF b (Q a) c (x₁ a)):= Menu.cnst _ n (fun i=> e _ (y i) ..)
 refine (Menu.total (univ:Finset spinSlot) (fun c i x=>roomF b (Q i) c (x₁ i) • (half (G i) j (R:=D) (J i c) true (w i x) + half (G i) j (R:=D) (J i c) false (w i x))) ?_).congr ?_
 · intro c _
   exact (m c).scale ((silk_half N L P sz j D (fun i=>J i c) w pay true).add (silk_half N L P sz j D (fun i=>J i c) w pay false))
 intro i r
 nth_rw 1 [show v i=nick (N i) (x₀ i) (x₁ i) from rfl] -- occurrence? x₀ not unfolded so v i only once
 rw [fee_vector,map_sum]; simp_rw [map_smul,basis_shell,map_sum,map_smul, cloth_column _ j (show LaurentRadius j (G i).count D from vA)]; rfl
omit pay vA y
private lemma trail_norm {N P:Side}(g:Ratio N P)(v:Ket (Iota g)):
   ‖trailK (switchG g).symm.toEmbedding v‖= ‖v‖:=by
 rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
 simp_rw [seamK,Equiv.toEmbedding_apply]; exact Equiv.sum_comp (switchG g).symm (fun i=> ‖v.ofLp i‖^2)
include pay vA y
lemma gifted (b:Bool)(v:(i:I)→Single (N i)):Menu (T:=fun i=> Ket (Single (P i))) (fun i x=> byMode (G i) j (Q i) (M i) (w i x) b (basisKet (v i))):=by
 simp_rw [byMode_eq]
 obtain ⟨t,l,u,e⟩:= linen N L P sz j D vA w pay M Q y b v
 refine ⟨Deal.along (fun i (x:Ket (Iota (G i)))=>trailK (switchG (G i)).symm.toEmbedding x) t ?_,l,u,fun i x=>?_⟩
 · intro ε z; refine ⟨ε,z,fun i x y p=>?_⟩; rw [dist_eq_norm,←map_sub,trail_norm]; simpa only [dist_eq_norm] using p
 rw [trail_norm]; exact e i x
end
end YM.CF.Buffered.Afterglow.Satin
#print axioms YM.CF.Buffered.Afterglow.Satin.gifted
