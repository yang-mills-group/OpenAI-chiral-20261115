import YM.CF.Brace.Band
/-! Section and transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase MeasureTheory Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B: Side}
-- normalized sea support
abbrev ground(m B:Side):= Wave (Single (CSide m B))
def rootsD(m B:Side)(j:ℕ)(M:Tulip.Male)(F:Duet m B)(U:Skin m B)(x:Sheen m B): ground m B:=sized (Complex.exp (-song m B F U x) • coneP j M U x)
def chant(m B:Side)(j:ℕ)(M:Tulip.Male)(F:Duet m B)(U:Skin m B): ground m B:= rootsD m B j M F U (starfish m B U (cue_from U).choose)
variable {F:Duet m B}{j:ℕ}{e p:ℝ}{M:Tulip.Male}(g:enoughV B e p)(he:0≤e)(h:Cane (CSide m B) j M e p F)
include g he h
lemma calm(x:Skin m B)(p':Guard x e)(X:Sheen m B)(u:Slow x (hook X) p): chant m B j M F x=rootsD m B j M F x X:=by
  let y:=starfish m B x (cue_from x).choose; have hv :=starK g he p' (cue_from x).choose_spec
  rw [chant,rootsD,rootsD,song_no g he h x p' y X hv u]
  rw [←(h.rhythm x p' y hv X u).1,smul_smul,←Complex.exp_add,show -(song _ _ F _ y+F x y X)+F x y X= -song _ _ F _ y by abel]
lemma heartS(x: Skin m B)(p':Guard x e)(k:IsStarProjection (spar j M x)):Sea (spar j M x) (chant m B j M F x):=by
  let y:=starfish m B x (cue_from x).choose; have hv:= starK g he p' (cue_from x).choose_spec
  rw [calm g he h x p' y hv]; constructor
  · rw [rootsD,sized, map_smul,map_smul,coneP,filled,←act_mul,(line_proj k).isIdempotentElem.eq]
  rw [rootsD,sized]
  have hf : ∀ z : ground m B,z≠0 → ‖(↑‖z‖:ℂ)⁻¹ • z‖=1 := by intro z hz; rw [norm_smul]; simp [hz]
  exact hf _ (smul_ne_zero (Complex.exp_ne_zero _) ((h.rhythm x p' y hv y hv).2))
lemma free_h (k:ContinuousOn (spar j M (N:=CSide m B)) {x|Guard x e}): ContinuousOn (fun x=>rootsD m B j M F x.1 x.2) (Chord m B e p):=by
  have ht: Continuous (postC (N:=CSide m B)) :=by
    refine continuous_matrix fun i j=>?_; unfold postC spotC; simp only [portW,Matrix.submatrix_apply];
    let f:Sheen m B → Site (CSide m B)→ Vect:=fun x=> (hook x ∘ node); have hv:Continuous f:=continuous_pi fun i=>continuous_subtype_val.comp (continuous_apply (node i)); exact ((C_cont.comp hv).matrix_elem _ _) -- tune
  let Z:= {x:Skin m B × Cue m|Guard x.1 e ∧ ZeroF m B x.1 x.2}
  let S:= {x:Skin m B|Guard x e}; let P:=song_c g he h
  let Y:= Chord m B e p
  have hz:ContinuousOn (fun x=>rootsD m B j M F x.1 x.2) Y:=by
    let V := fun x : Skin m B × Sheen m B=> (Complex.exp (-song m B F x.1 x.2)) • coneP j M x.1 x.2
    let K := Complex.continuous_exp.comp_continuousOn P.neg
    let f1:=fun i : Skin m B × Sheen m B=> spar j M i.1; let f2:=fun i:Skin m B × Sheen m B=>postC i.2
    have ht1:ContinuousOn f1 Y:= k.comp continuous_fst.continuousOn (fun i (g:i∈Y)=> g.1)
    have ht2:ContinuousOn f2 Y:=(ht.comp continuous_snd).continuousOn
    have ht3:ContinuousOn (fun i:Skin m B × Sheen m B=> coneP j M i.1 i.2) Y:= by
      let Z:=(Single (CSide m B))
      let f:=fun x=>(f1 x,f2 x); change ContinuousOn ((fun i:Op (Single (CSide m B)) × Op (Single (CSide m B))=> filled (n:=Single (CSide m B)) i.1 i.2) ∘ f) Y
      exact (filled_cont (n:=Single (CSide m B))).comp_continuousOn (ht1.prodMk ht2)
    have hu:ContinuousOn V Y:= K.smul ht3
    have H : ContinuousOn (fun x=> ((↑‖V x‖:ℂ)⁻¹)) Y:= by
      refine (Complex.continuous_ofReal.comp_continuousOn hu.norm).inv₀ ?_; intro i hi
      have he:V i ≠0:= smul_ne_zero (Complex.exp_ne_zero _) ((h.rhythm i.1 hi.1 _ hi.2 _ hi.2).2); simpa using he
    exact H.smul hu
  exact hz
lemma freezing (k:ContinuousOn (spar j M (N:=CSide m B)) {x|Guard x e}): ContinuousOn (chant m B j M F) {x|Guard x e}:=by
  let S:= {x:Skin m B|Guard x e}; let Y:= Chord m B e p
  let V: Set (Skin m B×Sheen m B):={x|Slow x.1 (hook x.2) p}
  have hp:IsOpen V:=by
    unfold V Slow; simp_rw [Set.setOf_forall]
    apply isOpen_iInter_of_finite; intro i; apply isOpen_iInter_of_finite; intro t
    apply isOpen_lt _ continuous_const; apply Continuous.norm
    have hz(i:Site (Domain m B)): Continuous (fun x:Skin m B×Sheen m B=>hook x.2 i):=by unfold hook; fun_prop
    let F : Skin m B × Sheen m B → E:=fun x=>x.1 (i,t)
    have hf:Continuous F:= (show Continuous (fun x:Skin m B=>x (i,t)) from continuous_apply _).comp continuous_fst
    have hh:=hf.prodMk (hz (i+step t)); have he:= turn_cont.comp hh; exact he.sub (hz i)
  intro U hU
  let u:= starfish m B U (cue_from U).choose; let f:= fun z:Skin m B=> (z,u); have hf: Continuous f:= continuous_id.prodMk continuous_const
  have hG: f U∈ V:= starK g he hU (cue_from U).choose_spec
  have hz: f U∈ Y:= ⟨hU,hG⟩
  have he': ∀ᶠ i in nhdsWithin U S, f i∈ Y:= Eventually.and (show ∀ᶠ i in nhdsWithin U S, Guard (f i).1 e from self_mem_nhdsWithin) (show ∀ᶠ i in nhdsWithin U S,Slow i (hook u) p from hf.continuousAt.continuousWithinAt (hp.mem_nhds hG))
  let K:=fun t:Skin m B × Sheen m B=>rootsD m B j M F t.1 t.2
  have hk: ContinuousWithinAt (K ∘ f) S U:= Tendsto.comp (free_h g he h k (f U) hz) (tendsto_nhdsWithin_iff.mpr ⟨hf.continuousAt.continuousWithinAt,he'⟩ : Tendsto f _ (nhdsWithin (f U) Y))
  exact hk.congr_of_eventuallyEq (he'.mono (fun i x=> calm g he h i x.1 u x.2)) (calm g he h U hz.1 u hz.2)
lemma phaseLift (U:Skin m B)(t:Guard U e)(x:Sheen m B)(u:Slow U (hook x) p)(v:ℝ)(k: ‖coneP j M U x‖=Real.exp v) : coneP j M U x=Complex.exp ((v:ℂ)+ Complex.I*(song m B F U x).im) • chant m B j M F U:=by
  rw [calm g he h U t x u,rootsD,sized,norm_smul, Complex.norm_exp,k,←Real.exp_add,Complex.ofReal_exp, smul_smul,smul_smul,←Complex.exp_neg,←Complex.exp_add,←Complex.exp_add]
  let z:=song m B F U x; rw [show (v:ℂ)+Complex.I * (z.im:ℂ) + -((((-z).re+v):ℝ):ℂ) + -z=0 by apply Complex.ext <;> simp<;>ring,Complex.exp_zero,one_smul]
end YM.CF.Brace
