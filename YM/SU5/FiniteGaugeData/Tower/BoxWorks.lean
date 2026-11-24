import YM.SU5.FiniteGaugeData.Tower.StationMaster
import YM.SU5.FiniteGaugeData.Tower.Sight
/-!
# Actual discrete slab algebra: adjoint, concatenate, length and translation

A nontrivial physical bounded operator realization even before continuum/contact
identifications. Here not stating phase faithfulness etc, only laws on entries
and concatenation (filtered widths, no overlap morphism). Use for cap algebra.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 350000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Set
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
local notation "L₀"=>Λ.R.L.val
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)
variable (Qt : Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=> Ark.Ht Y H Q.circuit j 0 strict C
local notation "Γ" i:max=> Tower.Field Y H i j 0 strict
local notation "κ" s:max=>actor Y H s Q.circuit j 0 strict C
local notation "Ε"=>advance Y H V Q.circuit j 0 strict C
local notation "θt" s:max i:max=> MeshClock.whenly (timeMesh Λ) s i
local notation "B" s:max f:max h:max=>boxOp Y H V s Q Qt j strict C _ f h
variable (w u:ℕ)(f:Entry Y H s j strict w)(g:Entry Y H s j strict u)(hw:0 < w)(hu:0 < u)
local notation "U"=>relocate K
local notation "c"=>ruler (tent Y H).B

lemma forward{S:Finset Cover}{t:ℕ}(q:Between K j (0:ℤ) t S): Tower.region j (meshface (Λ:=Λ) 0 s) (K).ℓ S:=by rw [area0]; exact fun i x=>(q i x).1
-- Between second integer coercion OK may fix
lemma timed_apply(t v:ℕ)(x:Γ t): (tick Y H t j 0 strict (2*v) x).val= U j (v:ℤ) x.val:=by
 change chime K j (Heat.gaugeShift Λ.block ((2*v:ℕ):ℤ)) x.val=chime K j (gaugeT K (v:ℤ)) x.val; unfold gaugeT; push_cast; rfl
private lemma entered_area{S W:Finset Cover}(a:Between K j 0 (ruler (tent Y H).B*(w:ℤ)) S)(l:Between K j 0 (ruler (tent Y H).B*(u:ℤ)) W):Between K j 0 (c*((w+u:ℕ):ℤ)) (S∪plow K j w W):=by
 have he:=l.relocate K j w; rw [add_zero] at he; have hp:= ruler_gene (K).B
 push_cast; rw [mul_add]
 exact pair_between K j a he (by positivity) (by simp [mul_nonneg hp.le])
noncomputable def edit:Entry Y H s j strict (w+u):=by
 let a:= tick Y H s j 0 strict (2*w) g.val
 let F:Γ s:=⟨f.val.val * a.val,Subalgebra.mul_mem (purpose ..) f.val.property a.property⟩
 refine ⟨F,?_⟩
 obtain ⟨S,h,t⟩:=f.property; obtain ⟨W,x,q⟩:=g.property
 have hh:InTest K true (plow K j w W) false a.val:=by unfold a; rw [timed_apply]; exact flow_port K j _ x
 exact ⟨S∪plow K j w W, (h.mono subset_union_left).mul (hh.mono subset_union_right),entered_area Y H j w u t q⟩
lemma editor : (edit Y H s j strict w u f g).val.val = f.val.val * U j (w:ℤ) g.val.val:=congrArg (fun r=>f.val.val*r) (timed_apply Y H j strict s w g.val)

include V C
lemma test_high (A₁ B₁:A→L[ℂ] A)(h:∀i:ℕ,s ≤ i →∀v:Γ i,A₁ ((κ i) v)=B₁ ((κ i) v)):A₁=B₁:=by
 apply _root_.YM.Kernel.Gram.by_bud C; intro x
 let n:=max s x.1; have hg:x.1 ≤ n:=le_max_right ..
 have he:=h n (le_max_left ..) (Raise Y H Q.circuit j 0 strict x.1 n hg x.2)
 rwa [join_actor Y H V Q.circuit j 0 strict C] at he

include Qt hw
local notation "T" i:max h:max x:max=>furnished Y H s Q j strict _ x i h
lemma refined_box(t:ℕ)(p:s≤t): B s f hw =boxOp Y H V t Q Qt j strict C (L₀^(t-s)*w) (T t p f) (Nat.mul_pos (pow_pos Λ.R.L.property _) hw):=by
 apply test_high Y H V t Q j strict C
 intro v e g
 rw [snatch Y H V s Q Qt j strict C w _ hw (p.trans e),snatch Y H V t Q Qt j strict C _ _ _ e]
 apply congrArg (κ v); apply Subtype.ext; rw [slab_eq,slab_eq,launch Y H V s Q j strict C w f t v p e]; change _= (Raise Y H Q.circuit j (0:ℤ) strict t v e _).val * U j _ g.val -- type motive
 congr 2
 rw [←mul_assoc,←pow_add,show v-t+(t-s)=v-s by omega]
lemma early_gate(t v:ℕ)(p:s≤t)(x:Γ t): Ε (θt s v) ((κ t) x)=(κ t) (tick Y H t j 0 strict (2*(L₀^(t-s)*v)) x):=by
 rw [advance_at,limited_time Y H V s Q.circuit j 0 strict C (2*v) p,amount,show L₀^(t-s)*(2*v)= 2*(L₀^(t-s)*v) from by ring]
include hu
lemma edit_comp : (B s f hw).comp (B s g hu) =boxOp Y H V s Q Qt j strict C _ (edit Y H s j strict w u f g) (by omega):=by
 apply test_high Y H V s Q j strict C; intro v p V1
 let a0:=edit Y H s j strict w u f g; let e:=v-s; let n:=L₀^e; let F:= T v p f; let G:= T v p g
 simp only [ContinuousLinearMap.comp_apply,snatch Y H V s Q Qt j strict C w f hw p,snatch Y H V s Q Qt j strict C u g hu p,snatch Y H V s Q Qt j strict C (w+u) (edit Y H s j strict w u f g) (by omega) p]
 -- above simp a0 RHS folded?
 apply congrArg (κ v); apply Subtype.ext
 rw [slab_eq,slab_eq,slab_eq, relocate_mul,relocate_sums K j _ _ ((exam j _ K ((purpose_ok ..).mp V1.property).1).1),←mul_assoc]
 change ((stream Y H D s e f.val.val)*((U j (n*w:ℕ)) (stream Y H D s e g.val.val)))*_=(stream Y H D s e a0.val.val)*(U j (n*(w+u):ℕ)) V1.val
 refine congrArg₂ (· * ·) ?_ ?_
 swap
 · rw [show n*(w+u)=n*w+n*u from mul_add ..,Nat.cast_add]
 change stream Y H D s _ _ *(U j (n*w:ℕ)) (stream Y H D s _ _) = stream Y H D s _ a0.val.val
 unfold a0; rw [editor]
 obtain ⟨S,x,ht⟩:=f.property; obtain ⟨W,h,t⟩:=g.property
 have he:= t.relocate K j (w:ℤ); rw [add_zero] at he
 have hx:= cover_between K Λ l rfl j (S:=S) (fun i v=>(ht i v).2) (M:=plow K j w W) (fun i v=>(he i v).1)
 unfold relocate; rw [woven_product Y H Q.circuit s _ x (flow_port K j _ h) hx]
 unfold gaugeT; rw [show (K).B=Λ.block from rfl,chime_X Y H V s j _ Q.circuit (aux_test h)]; unfold n e; push_cast
 rw [mul_left_comm _ (2:ℤ)]

-- increase width; can implement via edit with unit.
noncomputable def identity : Entry Y H s j strict w:= ⟨unity Y H j 0 strict s,∅,InTest.one,(fun _ h=>by simp at h)⟩
omit hu
lemma ticket_birth:(B s (identity Y H s j strict w) hw)= Ε (θt s w):=by
 apply test_high Y H V s Q j strict C; intro v p x
 rw [snatch Y H V s Q Qt j strict C w (identity Y H s j strict w) hw p,early_gate Y H V s Q Qt j strict C w hw v w p x] -- inspect
 apply congrArg (κ v); apply Subtype.ext
 rw [slab_eq,timed_apply]
 change stream Y H D s _ 1 *_=_; rw [woven_one Y H Q.circuit,one_mul]
-- select arbitrary discrete width increase by blank (right padding), and
-- left padding when translating inside slab. Also rotations/space pulls on
-- letter. Use for cap placements independent choices.
lemma shape_right(n:ℕ)(h:Entry Y H s j strict (w+n))(he:h.val.val=f.val.val):B s h (by omega)=(B s f hw).comp (Ε (θt s n)):=by
 rcases Nat.eq_zero_or_pos n with rfl| hn
 · have hr:h=f:=Subtype.ext (Subtype.ext he); rw [hr,MeshClock.when_zero,advance_source]; rfl
 rw [← ticket_birth Y H V s Q Qt j strict C n hn,edit_comp Y H V s Q Qt j strict C w n f _ hw hn]
 apply congrArg (fun x:Entry Y H s j strict (w+n)=>boxOp Y H V s Q Qt j strict C _ x (by omega)); apply Subtype.ext; apply Subtype.ext
 rw [editor]; unfold identity unity relocate; rw [chime_unit,mul_one]; exact he
lemma shape_left(n:ℕ)(h:Entry Y H s j strict (n+w))(he:h.val.val=U j (n:ℤ) f.val.val):B s h (by omega)=(Ε (θt s n)).comp (B s f hw):=by
 rcases Nat.eq_zero_or_pos n with rfl | hn
 · rw [MeshClock.when_zero,advance_source]
   have hh:0+w=w:=Nat.zero_add _
   apply test_high Y H V s Q j strict C; intro t p x
   change (B s h (by omega)) _=(B s f hw) _; rw [snatch Y H V _ Q Qt j strict C (0+w) h _ p,snatch Y H V s Q Qt j strict C w f hw p]; apply congrArg _; apply Subtype.ext; rw [slab_eq,slab_eq]; change stream Y H D s _ h.val.val*_ = stream _ _ _ _ _ f.val.val*(U j ((L₀^(t-s)*w:ℕ):ℤ) x.val); rw [he]; have hv: ((0:ℕ):ℤ)=0:= rfl; rw [hv,relocate_zero K j (test_entry ..)] -- finish arg
   congr 2; simp
 rw [← ticket_birth Y H V s Q Qt j strict C n hn,edit_comp Y H V s Q Qt j strict C n w _ f hn hw]
 apply congrArg (fun x:Entry Y H s j strict (n+w)=>boxOp Y H V s Q Qt j strict C _ x (by omega)); apply Subtype.ext; apply Subtype.ext
 rw [editor]; exact he.trans (one_mul _).symm

-- single transverse shift. 2* due spatial grid. every active axis commutes as needed.
noncomputable def alongS (a:Trans j)(b:ℤ):Entry Y H s j strict w:=by
 let F:= (sail Y H s j 0 strict _ a.property (2*b)) f.val
 refine ⟨F,?_⟩
 obtain ⟨S,h,i⟩:=f.property
 let W:=plow K a.val b S
 have h₁:InTest K true W false F.val:= flow_port K a.val _ h
 exact ⟨W,h₁, fun z p=>by obtain ⟨x,p',rfl⟩:= plow_stays K a.val b S p; rw [moves,if_neg (Ne.symm a.property)]; exact i x p'⟩
omit Qt V C hw in
lemma alongS_val(a:Trans j)(b:ℤ): (alongS Y H s j strict w f a b).val.val=U a.val b f.val.val:=rfl
local notation "Λ₀"=> ladder Y H V Q.circuit j 0 strict C
local notation "N" s:max i:max=>MeshClock.notch (timeMesh Λ) s i
local notation "φ" a:max i:max=> (((Λ₀).crew a).play i)
lemma shape_across (d:Trans j)(k':ℤ): (φ d (N s k')).comp (B s f hw)=(B s (alongS Y H s j strict w f d k') hw).comp (φ d (N s k')):=by
 apply test_high Y H V s Q j strict C; intro t v x
 let n:=t-s; let a':=alongS Y H s j strict w f d k'
 let m:= Λ.R.L.val^n
 change (φ d _) ((B s f _) _)= (B s a' _) ((φ d _) _)
 rw [snatch Y H V s Q Qt j strict C _ _ hw v,on_ladder,sailV_at Y H V s Q.circuit j 0 strict d.val d.property C (2*k') t v,sailV_at Y H V s Q.circuit j 0 strict d.val d.property C (2*k') t v,snatch Y H V s Q Qt j strict C _ a' hw v]
 apply congrArg _; apply Subtype.ext
 let v':=Heat.gaugeShift Λ.block (smill Λ s t (2*k'))
 change chime K d.val v' (slabT _ _ _ _ _ _ (T t v f) x).val=(slabT _ _ _ _ _ _ (T t v a') _).val
 rw [slab_eq,slab_eq,chime_product]; unfold relocate
 have hx:TestFamily K true x.val:=(exam j _ K ((purpose_ok ..).mp x.property).1).1
 rw [twin_slide d.val j _ _ hx.paid.choose_spec]; refine congrArg₂ (·*·) ?_ rfl
 change _ = stream Y H D s (t-s) a'.val.val
 unfold a'; rw [alongS_val]; unfold relocate gaugeT; rw [show (K).B=Λ.block from rfl,chime_X Y H V s d.val _ Q.circuit (test_entry ..)]; rfl

local notation "ω"=>floorV Y H Q.circuit j 0 strict C
lemma lays : (B s f hw) ω= (κ s) f.val:=by
 rw [vacua Y H V Q.circuit j 0 strict C s,snatch_equal]; apply congrArg _; apply Subtype.ext; rw [slab_eq]; unfold unity relocate; rw [chime_unit]; exact mul_one _
lemma locates(f:Γ s): inner ℂ ω ((κ s) f) = E s f.val:=by
 rw [vacua Y H V Q.circuit j 0 strict C s,stems Y H V]
 unfold unity; rw [mirror_unit]; exact congrArg _ (one_mul _)

-- box equals any single read: via Cloud analysis gets same finite signs.
lemma boxed_at:inner ℂ ω ((B s f hw) ω)=E s f.val.val:=by rw [lays, locates Y H V s Q Qt j strict C w hw] -- tune
end YM.CF.Buffered.Afterglow.Tower.SlabMark
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.boxed_at
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.edit_comp
#print axioms YM.CF.Buffered.Afterglow.Tower.SlabMark.shape_across
