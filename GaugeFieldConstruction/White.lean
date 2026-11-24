import GaugeFieldConstruction.Weather
/-!
# Solve the projected system and prove first-stage U4 stability
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
set_option synthInstance.maxSize 5500
open Function Module Set Filter Fathom Sailing
open scoped Topology BigOperators
variable {D W X : Type*} [AddCommGroup D] [Module ℝ D] [Module.Finite ℝ D]
    [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W] {H : Type*} [Group H] {p:Helm H} {w : Mount W} {r:Vap p w D}

private instance : Module.Finite ℝ G:= @FiniteDimensional.finiteDimensional_submodule ℝ _ _ _ _ _ _ -- check
local instance i₂ : AddCommGroup (C2 D):= @Submodule.addCommGroup ℝ _ _ _ _ _
local instance iP (r:Vap p w D) : AddCommGroup ↥(Patch r):= @Submodule.addCommGroup ℝ (C2 D) _ _ _ (Patch r)
local instance i4 : FiniteDimensional ℝ (C2 D):= @FiniteDimensional.finiteDimensional_submodule ℝ _ _ _ _ _ _
local instance i5 (r: Vap p w D) : FiniteDimensional ℝ ↥(Patch r):= @FiniteDimensional.finiteDimensional_submodule ℝ _ _ _ _ _ (Patch r)

-- speeds of section objects, as Dips
namespace Weather
variable {l:Filter X} {A:X→Weather r} {B: Weather r}
structure Track {r:Vap p w D} (l : Filter X) (A:X→Weather r) (B: Weather r): Prop where
  k x : Dips ℝ l (fun i=> (A i).k x) (B.k x)
  j x : Dips ℝ l (fun i=> (A i).j x) (B.j x)
namespace Track
variable (Q:Track l A B)
include Q in
lemma wide (x:X→ Wave r) (z:Wave r) (u:Dips ℝ l x z) (a):Dips ℝ l (fun k=> (A k).offer (x k) a) (B.offer z a) := by
  refine plus (Q.j a) (trav Q.k (fun i=> (x i).val a) (z.val a) ?_)
  exact excursion (maps u (Wave r).subtype) a
lemma dual (h : X→W) (j:X→W) {s t} (v:Dips ℝ l h s) (p:Dips ℝ l j t): Dips ℝ l (fun k=> w.l (h k) (j k)) (w.l s t):= trav (H:=fun k=> w.l (h k)) (h:=w.l s) (fun i=> excursion (maps v w.l) i) j t p
include Q
lemma zen (x:X→Wave r) (z: Wave r) (u:Dips ℝ l x z) (a v): Dips ℝ l (fun i=> (A i).active (x i) a v) (B.active z a v) := by
  apply (ringed Q.k B.faithful).2; simp_rw [activa]
  exact dual _ _ (Q.wide x z u _) (Q.k v)
-- Pullback representation of c2 onto fixed subspaces
omit Q in
def etch (x : X→Patch r) := fun i=> (x i).val.val
omit Q in
lemma paid_bits (x:X→Patch r) (z : Patch r) (p:∀ i j,Dips ℝ l (fun k=> (x k).val.val i j) (z.val.val i j)): Dips ℝ l x z:= by
  let Z : Patch r →ₗ[ℝ] Bile D:= (opposite D).subtype ∘ₗ (Patch r).subtype
  apply (ringed (p:=l) (f:=fun _=> Z) (L:=Z) (fun i=> Sailing.fixed (Z i)) (Subtype.val_injective.comp Subtype.val_injective)).2
  exact dotted (fun i=> dotted (fun j=> p i j))

lemma wind (x:Wave r): Dips ℝ l (fun k=> (A k).del x) (B.del x):= by
  refine paid_bits _ _ (fun i j=> ?_)
  change Dips _ _ (fun k=> (A k).active 0 i (x.val j)-(A k).active 0 j (x.val i)-x.val (bracket i j)) (B.active 0 i _- B.active 0 j _-x.val (bracket i j)); exact dif (dif (Q.zen (fun _=>0) 0 (Sailing.fixed 0) _ _) (Q.zen (fun _=>0) _ (Sailing.fixed 0) _ _)) (Sailing.fixed _)
lemma prize : Dips ℝ l (fun i=> (A i).rho) B.rho := by
  refine paid_bits _ _ (fun i j=> ?_); apply (ringed Q.k B.faithful).2; change Dips ℝ _ (fun k=> (A k).k ((A k).milled.val i j)) (B.k (B.milled.val _ _)); simp_rw [mill,tariff_v]
  exact dif (dual _ _ (Q.j i) (Q.j j)) (Q.j _)
lemma warms (x y: Wave r): Dips ℝ l (fun k=> (A k).ear x y) (B.ear x y):=by
  refine paid_bits _ _ (fun i j=>?_); apply (ringed Q.k B.faithful).2
  change Dips _ _ (fun k=> (A k).k (((A k).highQ x y).val i j)) (B.k ((B.highQ x y).val i j)); simp_rw [tide]
  exact chip (plus (dual _ _ (Q.k (x.val i)) (Q.k (y.val j))) (dual _ _ (Q.k (y.val i)) (Q.k (x.val j)))) (tendsto_const_nhds (x:=1/(2:ℝ)))
end Track

lemma probe {S:Tour D} (x y z : G): ∃ F:C2 D→ₗ[ℝ]D, ∀ i:C2 D,F i=S x (i.val y z)+ S y (i.val z x)+ S z (i.val x y)- (i.val (bracket x y) z +i.val (bracket y z) x+i.val (bracket z x) y):= by
  let M (b a:G):C2 D→ₗ[ℝ]D := LinearMap.applyₗ a ∘ₗ LinearMap.applyₗ b ∘ₗ (opposite D).subtype
  exact ⟨(S x ∘ₗ M y z)+(S y ∘ₗ M z x)+(S z ∘ₗ M x y)-(M (bracket x y) z+ M (bracket y z) x+M (bracket z x) y),fun _=>rfl⟩

def beacon (S:Tour D) (x y z:G): C2 D→ₗ[ℝ]D:= (probe (S:=S) x y z).choose
abbrev Bidder (D:Type*) [AddCommGroup D] [Module ℝ D]:= ((G×G)× G × (D→ₗ[ℝ]ℝ))
def porch (S:Tour D) : C2 D →ₗ[ℝ] Bidder D →ℝ := LinearMap.pi fun i=> i.2.2 ∘ₗ beacon S i.1.1 i.1.2 i.2.1
lemma doors (S:Tour D) (x:C2 D): porch S x=0 ↔ Cycle S x:= by
  constructor
  · intro h a b c
    apply sub_eq_zero.mp
    rw [← (probe (S:=S) a b c).choose_spec x]
    let G:= (Module.finBasis ℝ D).equivFun; apply G.injective; rw [map_zero]; ext1 i; exact congr_fun h ((a,b),c,(LinearMap.proj i) ∘ₗ G.toLinearMap)
  intro p; ext1 ⟨⟨i,j⟩,k,q⟩; change q ((probe _ _ _).choose _)=0; rw [Exists.choose_spec (probe (S:=S) i j k) x,p,sub_self,map_zero]
lemma door_panel (Q:X→Tour D) (h:Tour D) (v:∀ i j, Dips ℝ l (fun k=> Q k i j) (h i j)): Scores ℝ l (porch h) (fun i=>porch (Q i)) := by
  rintro ⟨⟨i,j⟩,k,q⟩ x
  change Tendsto (fun v=> q (beacon _ i j k x)) _ (𝓝 (q (beacon _ _ _ _ _)))
  unfold beacon; simp_rw [show ∀ o, (probe (S:=o) i j k).choose x=_ from fun o=>(probe ..).choose_spec x] -- syntax
  exact dif (plus (plus (v i (x.val j k)) (v j (x.val k i))) (v k (x.val i j))) (Sailing.fixed _) q

variable [Fintype H]
lemma lifting (K:Track l A B) (v:Hom w B.j) (s:Dome (B.active 0)): ∃ g:X→ Wave r,Dips ℝ l g 0 ∧ ∀ᶠ i in l, Hom w ((A i).offer (g i)):=by
  classical
  let S:= LinearMap.range B.del
  obtain ⟨R,hR⟩:= Submodule.exists_isCompl S
  let G:= S.projectionOnto R hR
  have h: Dips ℝ l (fun i=> G (A i).rho) 0 := by rw [← G.map_zero, ← B.pure v]; exact maps K.prize G
  have he :G ∘ₗ B.del=B.del.rangeRestrict:= LinearMap.ext fun i=> by change S.projectionOnto R hR (S.subtype (B.del.rangeRestrict i))=_; rw [Submodule.subtype_apply,Submodule.projectionOnto_apply_left]
  obtain ⟨f,hf,u⟩:= realization l B.del.rangeRestrict (fun i=> G ∘ₗ (A i).del) (B.ear.compr₂ G) (fun i=> (A i).ear.compr₂ G) (fun i=> G (A i).rho) B.del.surjective_rangeRestrict (fun x=> he ▸ maps (K.wind x) G) (fun i j=>maps (K.warms i j) G) h
  -- restrict probe to R and rank
  let Jt (S:Tour D): R→ₗ[ℝ] Bidder D→ℝ := porch S ∘ₗ (Patch r).subtype ∘ₗ R.subtype
  have hm:= door_panel _ _ (K.zen f 0 hf)
  have hi : Injective (Jt (B.active 0)):= by
    apply LinearMap.ker_eq_bot.mp; apply LinearMap.ker_eq_bot'.mpr; intro x e
    have hx:= (doors (B.active 0) x.val.val).mp e
    have hw:x.val∈S:=equiv₂ (B.pupil 0) (B.came v) s _ hx
    exact Subtype.ext ((Submodule.disjoint_def.mp hR.disjoint) _ hw x.property)
  have hv : Scores ℝ l (Jt (B.active 0)) (fun i=> Jt ((A i).active (f i))) := fun i x=> hm i (x.val.val)
  refine ⟨f,hf,?_⟩; filter_upwards [u,(insight hi hv).1] with i p q
  let T:=(A i); let v:=T.residual (f i)
  have h : v ∈ R:= by
    apply (Submodule.projectionOnto_apply_eq_zero_iff hR).mp
    unfold v residual; simp only [map_add]; exact p
  let y:R:=⟨v,h⟩
  have w: v=0:= congr_arg Subtype.val (q (show Jt _ y=Jt (T.active (f i)) 0 from ((doors ..).2 (T.bianchi (f i))).trans (map_zero _).symm))
  apply (tariff_zero _).mp; apply Subtype.ext; ext1 j; ext1 k
  rw [← score]
  change T.k (v.val.val _ _)=0; rw [w]; exact T.k.map_zero
end Weather
end YM.GaugeFieldConstruction.Apit
