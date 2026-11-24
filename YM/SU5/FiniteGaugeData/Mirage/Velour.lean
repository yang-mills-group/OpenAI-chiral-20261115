import YM.SU5.FiniteGaugeData.Mirage.Marin
import YM.SU5.FiniteGaugeData.Mirage.Roc
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Mirage
open Function Filter Lattice Cube Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
open Scroll Spire Peaks Tap Tenant Tulip Buffered Fock.Brique Window.Brique Largo
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N X:Side}{s r d w j:ℕ}{a C:ℝ}{σ τ:Window.Family}{S T U:Finset Cover}
local notation "Μ"=> Single N
local notation "Κ"=> FC (Single N)
open SU Dial Cascade Scree
local notation "T₀"=> Tset N
local notation "Q₀"=> (Tset N)ᶜ
variable (X: Support (More N))(M:Finset (Single N))
abbrev spotted (T:List (Single N)):=T.map fun i=>i.1.1
inductive Receipt (σ τ:Window.Family)(X:Support (More N))(M: Finset (Single N)): FC (Single N) → Prop where
| zero : Receipt σ τ X M 0
| stage {A:Κ} (t:List Μ)(v:t.toFinset⊆ M)(x:t≠[])(p:t.Nodup) : Chord σ τ N X (spotted t) A→Receipt σ τ X M A
| add {A B: Κ}: Receipt σ τ X M A→Receipt σ τ X M B → Receipt σ τ X M (A+B)
| smul {A: Κ} (v:ℂ): Receipt σ τ X M A → Receipt σ τ X M (v•A)
-- native accountability on taps spot list charges; can forget t for estimation.
variable {M X} {Y Z: FC (Single N)} (p:Receipt σ τ X M Y) (q:Receipt σ τ X M Z)
include p
lemma Receipt.mono {M':Finset Μ}(t:M⊆ M') : Receipt σ τ X M' Y := by
 induction p with| zero=> exact .zero| stage p h v l x=> exact .stage p (h.trans t) v l x| add _ _ a b=> exact a.add b| smul z _ a=> exact .smul z a
lemma Receipt.charges (i: Site (More N)→SU.E) : Receipt σ τ X M (flipsP i Y):= by
 induction p with| zero=> rw [map_zero]; exact .zero| stage p v t g s=> exact .stage p v t g (s.wind _)| add _ _ a b=> rw [map_add]; exact a.add b| smul z _ a=> rw [flipsP,twist_scalar]; exact .smul z a
lemma Receipt.veil (S':Support (More N))(h:X⊆ S')(v:∀ i∈ M,node i.1.1∈ S'): Reed.Fine (Tset N) (modesIn N S') false Y:=by
 induction p with
 | zero=>exact .empty _
 | stage t u p x H=> exact H.fines (fun i h=>by obtain ⟨k,y,rfl⟩:=List.mem_map.mp h; exact v _ (u (List.mem_toFinset.mpr y))) h
 | add _ _ a b=> exact a.add b
 | smul _ _ a=> exact a.scale _
lemma Receipt.raise (i:Single N)(v:i∉M) (h:i∈ capU σ i.1.1)(x:Ket (Single N))(g:withinM (lumen τ X) x): Receipt σ τ X (insert i M) (Y*(put i* remove x)):=by
 induction p with
 | zero=>rw [zero_mul]; exact .zero
 | stage t u p V H=> rw [←create_put]; exact .stage (i::t) (by rw [List.toFinset_cons]; exact insert_subset_insert _ u) (by simp) (List.nodup_cons.mpr ⟨fun h=>v (u (List.mem_toFinset.mpr h)),V⟩) (H.action _ _ _ (within_basis _ i h) g)
 | add _ _ a b=> rw [add_mul]; exact a.add b
 | smul _ _ a=> rw [Algebra.smul_mul_assoc]; exact .smul _ a
lemma Receipt.buys (f: FC (Single N)→ₗ[ℂ]ℂ) (t:f (centB N Y)≠0): ∃ t:List (Single N), t≠[] ∧ t.Nodup ∧ t.toFinset⊆ M ∧ ∃ A: FC (Single N), Chord σ τ N X (spotted t) A ∧ f A≠0 ∧ ∀ i:SU.E,orbitB A i=A:=by
 classical -- coe? guard use open scoped?
 induction p with
 | zero=>rw [map_zero,map_zero] at t; contradiction
 | @stage A Z v x h w=>
    let K:= (harpyM σ τ N X (spotted Z)).restrictScalars ℝ; have hz:centB N A∈K:= Convex.integral_mem (f:=orbitB A) K.convex (K.closed_of_finiteDimensional) (Eventually.of_forall fun i=>(w.wind (globalH N i): orbitB A i∈ K)) (orbit_integrable _)
    exact ⟨Z,x,h,v,centB N A, hz,t, cent_invariant _⟩
 | @add A B h h' a b=>
    rw [map_add,map_add] at t; by_cases z:f (centB N A)=0; · rw [z,zero_add] at t; exact b t
    exact a z
 | smul z _ a=> rw [map_smul,map_smul] at t; exact a fun h=> t (by rw [h,smul_zero])
omit p
variable {A:Op (Single N)}
-- formula B(c) polynomial. lean Diff conj not via norm. Rank proof p. produce .Buoyant.
abbrev rowdy (A:Op Μ)(x:Finset Μ)(c:ℂ): Κ:= star (starMark0 (Tset N) (star c • A) x)
def jargon (A:Op Μ)(i:Μ):Κ:= put i * remove (acts (cutM (Tset N)ᶜ * A) (basisKet i))
lemma hardly (c:ℂ)(i:Μ) : star (starBoost (Tset N) (star c • A) i)=1+c • jargon A i:=by
 rw [starBoost_star, Algebra.mul_smul_comm, act_smul]; unfold remove; rw [map_smul, star_smul, star_star,Algebra.mul_smul_comm]; rfl
lemma rowdyΘ (c:ℂ)(i:Μ)(x:Finset Μ)(v:∀ j∈x,i< j): rowdy A (insert i x) c= (rowdy A x c)*(1+c • jargon A i):=by
 unfold rowdy; rw [starMark0,column, sort_insert (·≤·) (fun j hj => (v j hj).le) (fun p=> lt_irrefl i (v i p)), List.map_cons,List.prod_cons, star_mul, hardly]; rfl
lemma rowdy_D (A:Op Μ)(S:Finset Μ) : Differentiable ℂ (rowdy A S):=by
 induction S using Finset.induction_on_min with
 | empty=> rw [show rowdy A ∅= fun _=>1 from funext (fun i=>by simp [rowdy,starMark0,column])]; exact differentiable_const _
 | insert x s h ih=> simp_rw [show (rowdy A (insert x s))=fun c=> _ from funext (fun c=> rowdyΘ c x s h)]; exact ih.mul ((differentiable_const _).add (differentiable_id.smul_const _))
lemma rowdyR (S:Finset Μ) (c:ℂ)(P:∀ i:Μ,i∈ S → i∈ capU σ i.1.1)(Q:∀ i:Μ,i∈ S →withinM (lumen τ X) (acts (cutM (Tset N)ᶜ*A) (basisKet i))) : Receipt σ τ X S (rowdy A S c-1):=by
 induction S using Finset.induction_on_min with
 | empty=> simp only [rowdy,starMark0,column,sort_empty,List.map_nil,List.prod_nil,star_one,sub_self]; exact .zero
 | insert i V h ih =>
    let R:= rowdy A V c; let W:= jargon A i; let Z:= insert i V; let ih':= ih (fun i t=>P _ (mem_insert_of_mem t)) (fun i t=>Q _ (mem_insert_of_mem t)); have hv:= P _ (mem_insert_self i V); have hz:= Q _ (mem_insert_self i V); have ht: Receipt σ τ X Z (1*W):= by
       refine .stage [i] (by simp [Z]) (by simp) (by simp) ?_; unfold W jargon; rw [← create_put]; exact Chord.action i.1.1 _ _ (within_basis _ _ hv) hz Chord.unit
    rw [rowdyΘ c i V h]; rw [show rowdy A V c * (1+c • jargon A i)-1=(R-1)+c • ((R-1)*W+1*W) from ?_]; swap; · unfold R W; rw [sub_mul,sub_add_cancel,mul_add,mul_one, Algebra.mul_smul_comm]; abel
    exact .add (ih'.mono (subset_insert ..)) (.smul c (.add (ih'.raise i (fun p=>lt_irrefl i (h i p)) hv _ hz) ht))
section
variable {F1 F2 G1 G2 W1 W2: Ruler (Mini N) (Fin r)}
variable {m:Tulip.Male}{U1 U2 L1 L2 : Finset Cover}{c1 c2 t:ℝ}
variable (P: Concert N (flatH m N) U1 L1 F1 G1 W1 c1 c2 t)
variable (Q: Concert N (flatH m N) U2 L2 F2 G2 W2 c1 c2 t)
variable (v:σ.2=τ.2)(t':σ.1≠τ.1)(U:Finset Sheet)(x:U⊆ genre σ)
local notation "B"=> eMark F1 G2 U σ.1 τ.1
local notation "V"=> (cibe (G2*F1ᴴ) σ.1 τ.1 U)
local notation "W"=> piggy (WalU N U1) U σ.1
local notation "X₂"=> Finset.image node (Finset.image (⇑(wrap N)) L2)
include P Q v t'
lemma E_D : Differentiable ℂ (eMark F1 G2 U σ.1 τ.1):=by
 rw [show eMark F1 G2 U σ.1 τ.1=rowdy V W from funext (fun i=> plot P Q _ _ t' U i)]; exact rowdy_D _ _
include x
lemma charm (i: Μ)(q:i∈ W): i∈ capU σ i.1.1:=by
 have he:tint U σ.1⊆ colors σ:=fun i h=>by rw [genre_color]; exact ⟨mem_singleton.mp (mem_product.mp h).1,x (mem_product.mp h).2⟩
 exact (is_cap ..).2 ⟨pigU σ.1 U q, (mem_filter.mp (he (mem_product.mp q).2)).2,rfl⟩
omit x v P Q t' in
lemma Charm_node (i:Μ)(q:i∈ W): i.1.1∈ Finset.image (wrap N) U1:=(mem_product.mp (mem_product.mp q).1).1
lemma R_shape (c:ℂ): Receipt σ τ X₂ W (eMark F1 G2 U σ.1 τ.1 c-1):=by
 rw [plot P Q _ _ t']; refine rowdyR W c (charm P Q v t' U x) fun i h=>?_; let S:= piggy (WalL N L2) U τ.1; have hz:cutM S* V= V:=by
    let hl:= (valJ P Q _ _ t' U 1); change _ ∧ cutM S* (star (1:ℂ) • V)= star (1:ℂ) • V at hl; simpa using hl.2
 have ht:V= cutM (Tset N)ᶜ*V:= (cutM_patch _ _ (pigL τ.1 U) _ hz).symm
 change withinM _ (acts (cutM _*_) _); rw [← ht]; unfold withinM; rw [←act_mul]; apply congrArg (fun f:Op Μ=>acts f _); refine cutM_patch S (lumen τ _) ?_ _ hz; intro i g
 have hf:=mem_product.mp g; have hp: tint U τ.1⊆ colors τ:= fun i h=>by
    rw [genre_color]; refine ⟨mem_singleton.mp (mem_product.mp h).1, ?_⟩; let t:= x (mem_product.mp h).2; rw [show genre τ=genre σ from (by unfold genre; rw [v])]; exact t
 exact (is_lumen ..).2 ⟨mem_compl.mp (pigL τ.1 U g), (mem_filter.mp (hp hf.2)).2,mem_image_of_mem node (mem_product.mp hf.1).1⟩
end
private lemma spots_cards (t:List (Single N))(u:SU.Slot)(h:∀ i∈t,i.2=u∧i∈Tset N)(p:t.Nodup)(k:Site N): (spotted t).count k≤ 2:=by
 let Z:= t.filter fun i=> i.1.1==k; have he: Z.length= (spotted t).count k:=by
    unfold Z spotted; simp only [List.count]; rw [List.countP_map,List.countP_eq_length_filter] -- tune
    rfl
 let A:SpinIdx→Single N:= fun a=> ((k,a),u); have h0:= p.filter (fun i:Single N=> i.1.1 == k); have hz:Z.toFinset⊆ plusHalf.image A:= by
    intro i q; obtain ⟨p,y⟩:= List.mem_filter.mp (List.mem_toFinset.mp q); obtain ⟨a,b⟩:= h i p; exact mem_image.mpr ⟨i.1.2,(grade_one ..).1 b, Prod.ext (Prod.ext (beq_iff_eq.mp y).symm rfl) a.symm⟩
 have hg: plusHalf.card≤2:=by decide
 rw [←he, ←List.toFinset_card_of_nodup h0]; exact (card_le_card hz).trans (card_image_le.trans hg)
lemma pigment_one (t:List (Single N))(u:Sheet)(p: t.toFinset⊆ piggy (WalU N S) {u} σ.1)(h:t.Nodup): ∀ k:Site N,(spotted t).count k ≤2:=by
 refine spots_cards t (αslot u σ.1) (fun i v=>?_) h ; let h:=p (List.mem_toFinset.mpr v); let h₁:=mem_product.mp (mem_product.mp h).2; exact ⟨Prod.ext (mem_singleton.mp h₁.1) (mem_singleton.mp h₁.2), pigU _ _ h⟩
#print axioms Receipt.buys
#print axioms pigment_one
#print axioms R_shape
#print axioms E_D
end YM.CF.Window.Mirage
