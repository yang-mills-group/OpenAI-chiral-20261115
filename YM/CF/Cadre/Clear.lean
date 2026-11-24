import YM.CF.Cadre.Coral
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Cadre
open Function Filter Topology Lattice Finset Palot
open scoped Classical
variable {A:Type*}[Fintype A][DecidableEq A]
local notation "ΣA"=> Palot.leaf A
local notation "ΣG"=> hook A
variable (Y:Palot.leaf A)(D O:Finset A)(F:hook A)
-- P supports meeting kernel leaf Y
variable (o:A)
-- Band Y: charge combined overlaps only. exact nonempty p.Y robe. fee all including kernel pure.
abbrev oreL (Y:ΣA)(o:A):Finset ΣG:=univ.filter fun G:ΣG=>∃ X∈spark o,G∈drum X Y ∅
lemma tok (Y X:ΣA)(p:F∈drum X Y ∅):F⊆blaze Y∧ X=glueV Y F:=by obtain ⟨_,h,v⟩:=(drum_p ..).mp p; exact ⟨fun i t=>mem_filter.mpr ⟨mem_univ _,h i t⟩,Subtype.ext v⟩
abbrev fiber(Y:ΣA)(o:A)(B:Finset ΣG):= oreL Y o∩B
lemma axes (f:ΣA→ΣG→ℝ)(B:Finset ΣG):
 (∑ X∈spark o,∑ G∈drum X Y ∅∩B,f X G)=∑ G∈fiber Y o B,f (glueV Y G) G:=by
 rw [sum_sigma']; refine sum_bij (fun (j:Sigma _) _=>j.2) ?_ ?_ ?_ ?_ -- sum_sigma' notation check
 · intro x h; obtain ⟨v,u⟩:= mem_sigma.mp h; obtain ⟨p,t⟩:=mem_inter.mp u; exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,x.1,v,p⟩,t⟩
 · rintro ⟨x,y⟩ h ⟨u,v⟩ p rfl; have hv:= (mem_inter.mp (mem_sigma.mp h).2).1; dsimp only; rw [(tok y Y x hv).2,(tok y Y u (mem_inter.mp (mem_sigma.mp p).2).1).2]
 · intro G t; obtain ⟨h,v⟩:=mem_inter.mp t; obtain ⟨X,r,u⟩:=(mem_filter.mp h).2; exact ⟨⟨X,G⟩,mem_sigma.mpr ⟨r,mem_inter.mpr ⟨u,v⟩⟩,rfl⟩
 rintro ⟨x,y⟩ h; exact congrArg (fun s=> f s y) ((tok _ _ _ (mem_inter.mp (mem_sigma.mp h).2).1).2)
abbrev tilt(Q:leaf A→ℝ)(P:ΣG):ℝ:=∏ j∈P,Q j
variable (Q P Xc:leaf A→ ℝ)(q:∀ i:leaf A,0≤Q i)(p:∀ i:leaf A,0≤P i)(h:∀ i:leaf A,0≤Xc i) -- Weight Xc at Hub; Q kernel.T
variable {b c d:ℝ}(xe:∀ (G:Palot.leaf A)(H:Palot.leaf A)(i:hook A), i∈drum G H ∅→ Xc G ≤ Xc H*tilt Xc i)(hp:∀ i:A,∑ X∈spark i,P X*Xc X ≤ b)
-- ≤C₁*b (card kernel) + C₀*∑ (card parents) silhouette
local notation "Xz"=> (P*Xc)
local notation "qz"=> (Q*Xc)
abbrev waveL(γ:ℝ)(S:ΣA):=Real.exp (S.val.card*γ)
local notation "ΩT"=> (qz * waveL (A:=A) b)
abbrev tweak (B:Finset ΣG)(K R:ΣA→ℝ)(X Y:ΣA):= (K Y)*∑ F∈ drum X Y ∅ ∩ B, tilt R F
include q p h xe
lemma tailT(B:Finset ΣG) : ∑ X∈spark o, tweak B Q P X Y*Xc X ≤ qz Y * ∑ i∈fiber Y o B,tilt Xz i:=by
 let W(X:ΣA)(F:ΣG):= Q Y*(tilt P F)*Xc X
 have he(X:ΣA): tweak B Q P X Y * Xc X= ∑ F∈drum X Y ∅ ∩ B,W X F:=by unfold tweak; rw [mul_sum,sum_mul]
 simp_rw [he]; rw [axes,mul_sum]; apply sum_le_sum; intro i u; obtain ⟨X,hx,v⟩:=(mem_filter.mp (mem_inter.mp u).1).2
 rw [← (tok i Y X v).2]; apply (mul_le_mul_of_nonneg_left (xe _ _ _ v) (mul_nonneg (q _) (prod_nonneg fun j _=>p _))).trans; simp only [tilt,Pi.mul_apply, prod_mul_distrib]; change _≤ _; exact le_of_eq (by ring)
omit q p h xe
abbrev farW(A:Type*)[DecidableEq A][Fintype A]: Finset (hook A):= univ.filter fun G=>G.Nonempty
include q p h xe hp
local notation "W7"=> (farW A)
abbrev ode0(X Y:ΣA):= tweak (farW A) Q P X Y
-- nonempty estimate for each kernel and root
lemma aura : ∑ X∈spark o, ode0 Q P X Y*Xc X ≤ (if o∈Y.val then ΩT Y * ((Y.val.card:ℝ)*b) else 0) + ΩT Y*∑ X∈spark o∩blaze Y,Xz X:=by
 let U:=fiber Y o W7; have hx:0 ≤ Xz:=fun i=>mul_nonneg (p _) (h _); have hz(Y:ΣA):0≤ qz Y:=mul_nonneg (q _) (h _); have hw :0 ≤ ΩT Y:=mul_nonneg (hz _) (Real.exp_pos ..).le
 have ha(T:ΣG)(p:T∈U):∃ X:ΣA,o∈X.val∧T∈drum X Y ∅:=by obtain ⟨X,v,w⟩:= (mem_filter.mp (mem_inter.mp p).1).2; exact ⟨X,(mem_filter.mp v).2,w⟩
 have H(T:ΣG)(p:T∈U): T⊆blaze Y:=let ⟨_,_,w⟩:=ha T p;(tok T _ _ w).1 -- existential elim
 refine (tailT Y o Q P Xc q p h xe W7).trans ?_; split_ifs with g
 · refine le_trans ?_ (le_add_of_nonneg_right (mul_nonneg hw (sum_nonneg fun i _=> hx i)))
   have ht:=cop Y (P*Xc) hx (blaze Y) b (fun i _=>hp i) U H (fun F p'=>by obtain ⟨a,v⟩:=(mem_filter.mp (mem_inter.mp p').2).2; exact ⟨a,H _ p' v,v⟩)
   have he:= ht.trans (mul_le_mul_of_nonneg_right (beam Y (P*Xc) hx b (fun i _=>hp i)) (Real.exp_pos ..|>.le))
   change qz Y* _≤ _; exact (mul_le_mul_of_nonneg_left he (hz _)).trans_eq (by rw [mul_comm (_*b), ← mul_assoc]; rfl)
 rw [zero_add]; have ht:=cop Y (P*Xc) hx (spark o ∩ blaze Y) b (fun i _=>hp i) U H (fun F p'=>?_); swap
 · obtain ⟨X,u,v⟩:= ha F p'; have hv: X=glueV Y F:= (tok F _ _ v).2; obtain ⟨j,t,hj⟩:=mem_biUnion.mp ((mem_union.mp (show o∈ Y.val∪robe F from (show o∈(glueV Y F).val from hv ▸ u))).resolve_left g); exact ⟨j,mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hj⟩, H _ p' t⟩,t⟩
 refine (mul_le_mul_of_nonneg_left ht (hz _)).trans_eq ?_; rw [mul_comm _ (Real.exp _),←mul_assoc]; rfl
end YM.CF.Cadre
