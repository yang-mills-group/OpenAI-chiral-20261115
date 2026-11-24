import YM.SU5.FiniteGaugeData.Cirrus.Marquis
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison
open Mink Mink.General Vp.Folio
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)(o:‖Ω.val‖=1)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)
local notation "a"=>timeAxis
variable {m n:ℕ} (x:Points m)(y:Points n)(z:Points (m+n))(u:Fin m→G.Chip)(v:Fin n→ G.Chip) (L: List (Fin m))(R:List (Fin n))(b:Axis)
-- blend pointSp (word concatenation, not choosing a chronology)
abbrev mingle (x:Points m)(y:Points n):Points (m+n):= points (Fin.append x.ofLp y.ofLp)
local notation "ℓ"=> mingle x y
local notation "g"=> Fin.append u v
@[simp] lemma M_left (i:Fin m): (mingle x y) (Fin.castAdd n i)=x i:=Fin.append_left x.ofLp y.ofLp i
@[simp] lemma M_right (i:Fin n): (mingle x y) (Fin.natAdd m i)= y i:= Fin.append_right x.ofLp y.ofLp i
lemma coilZ (x:Points n)(L: List (Fin n))(p:L.Perm (Each n))(h:ProofOrder x b L): Injective (clockV b x):=by
 have hv:(List.map (clockV b x) L).Nodup:= List.Pairwise.nodup (List.pairwise_map.mpr h); apply List.nodup_ofFn.mp (by rw [List.ofFn_eq_map]; exact (p.map _).nodup_iff.mp hv)
lemma clockLft(i:Fin m): clockV b (mingle x y) (Fin.castAdd n i)=clockV b x i:=by simp [clockV]
lemma clockRgt(i:Fin n): clockV b (mingle x y) (Fin.natAdd m i)=clockV b y i:=by simp [clockV]
lemma splitOK (p: (mingle x y)∈ conf (m+n)) : x∈conf m∧ y∈conf n :=by
 constructor
 · intro i j h; have he: Fin.castAdd n i= Fin.castAdd n j:=p ((M_left x y i).trans (h.trans (M_left x y j).symm)); simpa using he
 intro i j h; have he:Fin.natAdd m i=Fin.natAdd m j:=p ((M_right x y i).trans (h.trans (M_right x y j).symm)); simpa using he
lemma splitClock (p:Injective (clockV b (mingle x y))) : Injective (clockV b x)∧ Injective (clockV b y):=by
 constructor
 · intro i j h; have he:=p ((clockLft x y b i).trans (h.trans (clockLft x y b j).symm)); simpa using he
 intro i j h; have he:=p ((clockRgt x y b i).trans (h.trans (clockRgt x y b j).symm)); simpa using he
local notation "s₁"=> L.map (Fin.castAdd n)
local notation "s₂"=> R.map (Fin.natAdd m)
lemma clockWin (p:ProofOrder x b L)(k:ProofOrder y b R)(z:∀ (i:Fin m)(j:Fin n),clockV b x i<clockV b y j): ProofOrder (mingle x y) b (s₁++s₂):=by
 unfold ProofOrder Sau; rw [List.pairwise_append,List.pairwise_map,List.pairwise_map]
 simp only [clockLft, clockRgt]; refine ⟨p,k,?_⟩; intro i V j y'; obtain ⟨i,t,rfl⟩:= List.mem_map.mp V; obtain ⟨j,k,rfl⟩:=List.mem_map.mp y'; rw [clockLft,clockRgt]; exact z i j
-- presentation Perm
lemma paintAll (p:L.Perm (Each m))(q:R.Perm (Each n)):(s₁++s₂).Perm (Each (m+n)) := by
 apply ((p.map _).append (q.map _)).trans; apply List.Perm.of_eq
 unfold Each; rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, ← List.ofFn_fin_append, show (Fin.append (@Fin.castAdd m n) (Fin.natAdd m)) = id from ?_]; simp [List.ofFn_eq_map]
 refine funext (Fin.addCases (fun i=> Fin.append_left _ _ _) (fun i=> Fin.append_right _ _ _))
local notation "W"=> G.Sr S Ω (mingle x y) (g)
lemma heapL: W (s₁)= G.Sr S Ω x u L:=by
 apply congrArg (fun v=>inner ℂ Ω.val (v Ω.val)) (α:=H.Op); apply Eq.symm; apply mappingF; all_goals intros; simp [Canopy.senses, rho, Canopy.credit, clockLft]
lemma heapR: W (s₂)= G.Sr S Ω y v R:=by
 apply congrArg (fun v=>inner ℂ Ω.val (v Ω.val)) (α:=H.Op); apply Eq.symm; apply mappingF; all_goals intros; simp [Canopy.senses, rho, Canopy.credit, clockRgt]
-- Eu prices $$ornate all non-coinciding points.$
local notation "K₀" t:max=> G.ornate S Ω t
def harmony :Prop := G.ornate S Ω (mingle x y) (Fin.append u v)=(K₀ x) u*(K₀ y) v
variable (A:Pale S Ω G J K)(B:G.Earned S Ω)(z₁:∀ i,(u i).fst∈ J)(z₂:∀ i,(v i).fst∈ K)
include hΩ o A B z₁ z₂
lemma adorn (p:L.Perm (Each m))(q:R.Perm (Each n))(r:ProofOrder x a L)(k:ProofOrder y a R)(z:∀ (i:Fin m)(j:Fin n),clockV a x i<clockV a y j): harmony S Ω G x y u v:=by
 let v₀:=clockWin x y L R a r k z; unfold harmony; rw [B.realRoad _ _ _ _ (paintAll L R p q) v₀, B.realRoad _ _ _ _ p r,B.realRoad _ _ _ _ q k, stately S Ω hΩ o G J K _ _ _ _ A v₀ _ _]; rw [heapL,heapR]; all_goals intro i v'; obtain ⟨i,T',rfl⟩:=List.mem_map.mp v'; first| simp [Fin.append_left,z₁,z₂]
omit hΩ o A z₁ z₂
omit B in
lemma zeroMove (u:Points n): moving 0 u =u:= PiLp.ext fun i=> add_zero _
lemma rotates (s:SO) (v₀:(mingle x y) ∈ conf (m+n))(e:harmony S Ω G (turnO s.val x) (turnO s.val y) (G.stampE s u) (G.stampE s v)): harmony S Ω G x y u v := by
 let f:= Fin.append u v
 have r: Fin.append (G.stampE s u) (G.stampE s v)=G.stampE s (g):=by
    apply funext; apply Fin.addCases; all_goals intro i; simp [Canopy.stampE]
 have t:mingle (turnO s.val x) (turnO s.val y)=turnO s.val (mingle x y):=by apply PiLp.ext; apply Fin.addCases; all_goals intro i; simp [turnO];
 have he(n:ℕ)(x:Points n)(p:x∈conf n)(w:Fin n→G.Chip): (K₀ x) w=G.ornate S Ω (turnO s.val x) (G.stampE s w):= zeroMove (turnO s.val x) ▸ B.Euclidean n x p w s 0
 unfold harmony at *; rw [r,t] at e; rw [he _ _ v₀, he m x (splitOK x y v₀).1, he n y (splitOK x y v₀).2]; exact e
#print axioms adorn
#print axioms rotates
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
