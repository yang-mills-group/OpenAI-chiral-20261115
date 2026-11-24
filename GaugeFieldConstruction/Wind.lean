import GaugeFieldConstruction.White
/-!
# Choose coherent frames for the projection kernels; use the section theorem
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Function Module Set Filter Stage Fathom Sailing
open scoped Topology BigOperators
variable {D W H X: Type*} [Group H] {p:Helm H} [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    [AddCommGroup D] [Module ℝ D] [Module.Finite ℝ D] {w : Mount W}
variable (P:H→*Endr W) [Fintype H]

-- transform D subspace. late
 lemma maritime {s : D→ₗ[ℝ]W} (h:Injective s) (v:∀ i x,P i (s x)∈LinearMap.range s):∃ A:H→*Endr D, ∀ i x,s (A i x)=P i (s x):= by
  obtain ⟨L,hL⟩:= s.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr h)
  let t i:= L ∘ₗ P i ∘ₗ s
  have he i x:s (t i x)=P i (s x):= by
    change s (L (P i (s x)))=_; obtain ⟨y,p⟩:=v i x; rw [← p]; rw [show L (s y)= y from LinearMap.congr_fun hL y]
  refine ⟨{ toFun:= t
            map_mul':=?_
            map_one':=?_ }, he⟩ -- induction
  · apply LinearMap.ext; intro i; apply h; rw [he,map_one]; rfl
  intro x y; apply LinearMap.ext; intro i; apply h; rw [Module.End.mul_apply,he,he,he,map_mul]; rfl

lemma ferry (P:H→*Endr W) {l:Filter X} [l.NeBot] (G:X→D→ₗ[ℝ]W) (s:D→ₗ[ℝ] W) (h:Injective s)
    (u:∀ i,Dips ℝ l (fun k=> G k i) (s i)) (v:∀ k i x,P i (G k x)∈ LinearMap.range (G k)):
    ∀ i x,P i (s x)∈ LinearMap.range s:= by
  intro i x; choose H e using fun k=> v k i x
  have T:Dips ℝ l (fun k=> G k (H k)) (P i (s x)):= Sailing.constant (maps (u x) (P i)) (Eventually.of_forall fun k=> (e k).symm)
  obtain ⟨A,_,p⟩:= grows s G h u H _ T; exact ⟨A,p⟩

lemma dues (Q:H→*Endr D) (A:X→ D→ₗ[ℝ] W) (s:D→ₗ[ℝ] W) (v: Filter X)
    (h:Injective s) (u:∀ i,Dips ℝ v (fun k=> A k i) (s i)) (p:∀ k i x,P i (A k x)∈LinearMap.range (A k)) (Hq:∀ k x,s (Q k x)=P k (s x)):
    ∃ L:X→D→ₗ[ℝ]W,(∀ k x g,L k (Q g x)=P g (L k x)) ∧ (∀ k,LinearMap.range (L k) ≤ LinearMap.range (A k)) ∧
      (∀ i,Dips ℝ v (fun k=> L k i) (s i)) ∧ ∀ᶠ k in v,LinearMap.range (L k)=LinearMap.range (A k) ∧ Injective (L k):=by
  let c:ℝ := Fintype.card H; have he:c≠0:=by unfold c; norm_cast; exact Fintype.card_pos.ne'
  let L (k:X): D→ₗ[ℝ] W := c⁻¹ • ∑ g:H,P g ∘ₗ A k ∘ₗ Q g⁻¹
  have hv k x:L k x=c⁻¹ • ∑ g:H,P g (A k (Q g⁻¹ x)):= by unfold L; rw [LinearMap.smul_apply,LinearMap.sum_apply]; rfl
  have Z (k:X):LinearMap.range (L k)≤ LinearMap.range (A k):=by
    rintro _ ⟨x,rfl⟩; rw [hv]; exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _=> p k i _)
  have z i:Dips ℝ v (fun k=> L k i) (s i):= by
    have e (g:H): P g (s (Q g⁻¹ i))=s i:= by rw [Hq,again]
    have Y := chip (gathers (Finset.univ:Finset H) (fun (g:H) _=> maps (u (Q g⁻¹ i)) (P g))) (tendsto_const_nhds (x:=c⁻¹)) -- tune binder
    simp_rw [e] at Y; rw [Finset.sum_const,Finset.card_univ,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ he,one_smul] at Y
    exact Sailing.constant Y (Eventually.of_forall fun k=> (hv k i).symm)
  refine ⟨L,fun k x g=> ?_, Z,z,(ringed z h).1.mono fun i v=> ?_⟩
  · rw [hv,hv,map_smul,map_sum]; congr 1
    let h (a:H):= P a (A k (Q a⁻¹ (Q g x)))
    have hu (s:H): h (g*s)=P g (P s (A k (Q s⁻¹ x))):= by unfold h; rw [mul_inv_rev,map_mul,map_mul]; simp only [Module.End.mul_apply]; rw [again']
    rw [show (∑ s:H,h s) = _ from (Equiv.sum_comp (Equiv.mulLeft g) h).symm]; exact Finset.sum_congr rfl fun i _=>hu i
  refine ⟨Submodule.eq_of_le_of_finrank_le (Z i) ?_,v⟩; rw [LinearMap.finrank_range_of_inj v]; exact LinearMap.finrank_range_le (A i) -- check

omit [Fintype H] [Module.Finite ℝ D] [Module.Finite ℝ W] in
def Dome.pull {α : Tour W} (G:Dome α) (u:D→ₗ[ℝ]W) (v:Injective u) (S:Tour D) (h:∀ i x,u (S i x)=α i (u x)): Dome S where
  form:=G.form.compl₁₂ u u
  pos x p:= G.pos _ (fun t=> p (v (t.trans u.map_zero.symm)))
  sym x y:=G.sym _ _
  neg i x y:=by change G.form (u _) (u _)= -G.form (u _) (u _); rw [h,h,G.neg]

structure Turbine (p:Helm H) (w:Mount W) (P:H→*Endr W) where
  s:C1 W
  joins:s∈ fixed (gr₁ p P)
  R:Submodule ℝ W
  fixedP i u:u∈R→P i u∈R
  fold i x:x∈R→ w.l (s i) x∈R
  in_ (i j:G): (tariff w s).val i j∈R
  cross x y:x∈R→y∈R→w.l x y∈R
-- integrate everything
lemma beacon (T :ℕ→Turbine p w P) (u_cov:∀ g a b,P g (w.l a b)=w.l (P g a) (P g b))
    (S:C1 W) (z:Hom w S) (B:Dome (w.l ∘ₗ S)) (x:∀ a,Dips ℝ atTop (fun k=> (T k).s a) (S a))
    (u:∀ i, finrank ℝ (T i).R=finrank ℝ D): -- dummy D_ remove
    ∃ g:ℕ→ℕ,StrictMono g ∧ ∃ h:ℕ→ C1 W,(∀ i,Dips ℝ atTop (fun k=>h k i) (S i)) ∧
      ∀ i,h i∈ fixed (gr₁ p P) ∧ Hom w (h i) ∧ ∀ x,h i x-(T (g i)).s x∈ (T (g i)).R:=by
  classical
  let f (i:ℕ) := LinearEquiv.ofFinrankEq D ((T i).R) (u i).symm
  let a i:= (T i).R.subtype ∘ₗ (f i).toLinearMap
  obtain ⟨b,hb,i,m,v,hv⟩:= priceSweep a (fun i=> show Injective (a i) from Subtype.val_injective.comp (f i).injective)
  let L j:=a (i j) ∘ₗ (v j).toLinearMap
  have p0 j:LinearMap.range (L j) = (T (i j)).R:= by
    rw [show L j=(T (i j)).R.subtype ∘ₗ ((v j).trans (f (i j))).toLinearMap from rfl,LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range ..)] -- check
    exact Submodule.range_subtype _
  have p' k g x:P g (L k x) ∈LinearMap.range (L k):=by rw [p0 k]; exact (T (i k)).fixedP g _ ((p0 k) ▸ LinearMap.mem_range_self _ _)
  obtain ⟨U,V⟩:=maritime _ hb (ferry P L _ hb hv p')
  obtain ⟨F,hF,_,Hq,K⟩:= dues P U L _ atTop hb hv p' V
  let r : Vap p w D :=⟨U,P,u_cov⟩
  obtain ⟨W,hW⟩:= b.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hb) -- W shadow
  -- build limit
  let q (j) := i j
  have hx k:Dips ℝ atTop (fun j=> (T (i j)).s k) (S k):=subs (x k) i m.tendsto_atTop
  let R: Weather r:=⟨b,hb,W,(fun x=>LinearMap.congr_fun hW x),fun i x=>(V i x).symm,S,?_,?_,?_,fun i j=>by rw [(tariff_zero _).mpr z]; exact Submodule.zero_mem _⟩
  case refine_1 =>
    apply (fix₁ S).mpr; intro g i
    refine individual (Sailing.constant (maps (hx i) (P g)) ?_) (hx (p.A g i))
    exact Eventually.of_forall fun j=> (fix₁ _).mp (T _).joins g i
  case refine_2 =>
    intro x y
    have H k:w.l (L k x) (L k y)∈LinearMap.range (L k):=by rw [p0]; exact (T _).cross _ _ ((p0 k) ▸ LinearMap.mem_range_self _ _) ((p0 k) ▸ LinearMap.mem_range_self _ _)
    choose u e using H
    obtain ⟨A,v,p⟩:= grows b L hb hv u _ (Sailing.constant (Weather.Track.dual (w:=w) _ _ (hv x) (hv y)) (Eventually.of_forall fun i=> (e i).symm))
    exact ⟨A,p⟩
  case refine_3 =>
    intro j x
    have H k:w.l ((T (i k)).s j) (L k x) ∈LinearMap.range (L k):= by rw [p0]; exact (T _).fold _ _ ((p0 k) ▸ LinearMap.mem_range_self _ _)
    choose u e using H
    obtain ⟨A,v,p⟩:= grows b L hb hv u _ (Sailing.constant (Weather.Track.dual (w:=w) _ _ (hx j) (hv x)) (Eventually.of_forall fun i=> (e i).symm))
    exact ⟨A,p⟩
  -- after cutting tail can't rewrite (range) occurrence parallel
  obtain ⟨k,h⟩:= eventually_atTop.mp K
  let J (u:ℕ):=u+k
  have M :StrictMono J:=fun i j p=>Nat.add_lt_add_right p k
  let j:=i ∘ J
  have HE i:Injective (F (J i)):= (h _ (Nat.le_add_left ..)).2
  have Y u : LinearMap.range (F (J u))=(T (j u)).R:= (h (J u) (Nat.le_add_left ..)).1.trans (p0 _)
  choose y hy using fun i=> (F (J i)).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (HE i))
  let A (i:ℕ): Weather r :=
    { k:= F (J i), faithful:= HE i
      L:= y i, retract x:= LinearMap.congr_fun (hy i) x
      h g x:=(hF (J i) x g).symm
      j:=(T (j i)).s,kisses:= (T _).joins
      fold s x:= (Y i) ▸ (T _).fold _ _ ((Y i) ▸ LinearMap.mem_range_self _ _)
      cross x z:= (Y i) ▸ (T _).cross _ _ ((Y i) ▸ LinearMap.mem_range_self _ _) ((Y i) ▸ LinearMap.mem_range_self _ _)
      match_ x y:= (Y i) ▸ (T _).in_ x y }
  have hA:Weather.Track atTop A R:= ⟨fun x=> subs (Hq x) J M.tendsto_atTop,fun a=>subs (hx a) J M.tendsto_atTop⟩
  have u k x : R.k (R.active 0 k x)=w.l (R.j k) (R.k x):= by rw [R.activa,R.offer0]
  obtain ⟨g,hg,hm⟩:= Weather.lifting hA z (B.pull b hb (R.active 0) u) -- S=R.j
  obtain ⟨u,w⟩:= eventually_atTop.mp hm
  let t i:=i+u
  have hl : StrictMono t:= fun x y h=>Nat.add_lt_add_right h u
  refine ⟨j ∘ t,(m.comp M).comp hl,fun x=> (A (t x)).offer (g (t x)),fun i=>?_,fun i=>⟨(A _).achieve _,w _ (Nat.le_add_left ..),fun x=>?_⟩⟩
  · have v:=subs (hA.wide _ _ hg i) t hl.tendsto_atTop; rw [Weather.offer0] at v; exact v
  change (((T _).s) x + F (J (t i)) ((g _).val x)-(T (j (t i))).s x)∈ (T (j (t i))).R; rw [add_sub_cancel_left]; exact Y _ ▸ LinearMap.mem_range_self _ _
end YM.GaugeFieldConstruction.Apit
