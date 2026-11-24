import YM.SU5.SatinWard.Resolution.Andesite
import YM.SU5.SatinWard.Resolution.Timpani
import GaugeFieldConstruction.StencilUpright
/-!
 # Complex completion, dialect accounting. Caller supplies *actual Dovetail.Council*. Orbit Sector.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 15000
set_option maxHeartbeats 580000
noncomputable section
namespace YM.SatinMark.Scene
open CF CF.QuadClock ShapeLab SoulField
open Function Set Filter Finset Complex
open _root_.YM.SatinWFixed Andesite Carton
open scoped BigOperators Topology ContDiff
open Classical in
noncomputable abbrev choralLeg_st (i:Axis)(v:Wage3):(Option (Axis×Wage3)→ℂ):= herald (some (i,v)) 1 -- matches trueCorner
noncomputable abbrev gaugeOrigin_st : Option (Axis× Wage3)→ℂ:= herald none 1
variable {L:Type*}
noncomputable abbrev takesPolySt (z:Soul): (Wage3→ℂ) := fun x=>↑(z x)
noncomputable def cPay_st {ι:Type*} [Fintype ι] {A:Type*}[AddCommGroup A][Module ℂ A] (g:ι→ A): (ι→ℂ)→ₗ[ℂ] A:= ∑ j:ι, (LinearMap.proj j).smulRight (g j)
lemma pol_values_st{L:Type*}[Fintype L] {A:Type*}[AddCommGroup A][Module ℂ A]{f:L→A} (x:L→ℂ) : cPay_st f x=∑ u:L,x u • f u:=by simp only[cPay_st,LinearMap.sum_apply]; rfl
lemma col_values_st (i:Axis)(x:Soul) : cPay_st (choralLeg_st i) (takesPolySt x)=∑ v:Wage3, (x v:ℂ) • choralLeg_st i v:=pol_values_st _
lemma at_values_st (i:Wage3){A:Type*} [AddCommGroup A][Module ℂ A](g:Wage3→A): cPay_st g (takesPolySt (ShapeLab.leg i))= g i:=by rw [pol_values_st,sum_eq_single i]<;> simp_all [takesPolySt,ShapeLab.leg]
local notation "ΣK"=> (Option (Axis×Wage3))
abbrev dialectType_st := Option (Axis×Wage3) →ℂ
local notation "Ω"=> gaugeOrigin_st
local notation "εL" i:max=> cPay_st (choralLeg_st i)
lemma vertex_st (i:Axis)(z:Wage3→ℂ)(t:Wage3) : ((εL i) z) (some (i,t))=z t:=by
 rw [pol_values_st, Finset.sum_apply, sum_eq_single t]; · simp
 · intro j _ h; rw [Pi.smul_apply, choralLeg_st, herald_no (by rintro ⟨⟩; contradiction : some (i,t) ≠ some (i,j))]; simp
 simp
lemma vanish_st (i j:Axis)(z:Wage3→ℂ)(p:i≠j)(t:Wage3) : ((εL i) z) (some (j,t))=0:=by
 rw [pol_values_st, Finset.sum_apply]; refine sum_eq_zero fun a _=> ?_; rw[Pi.smul_apply, choralLeg_st, herald_no (by rintro ⟨⟩; contradiction : some (j,t)≠some (i,a)),smul_zero]
lemma vertexNone_st (i:Axis)(z:Wage3→ℂ) : ((εL i) z) none=0:=by
 rw [pol_values_st,Finset.sum_apply]; refine sum_eq_zero fun a _=>?_ ; rw [Pi.smul_apply,choralLeg_st,herald_no (by simp : ¬ none=some (i,a)), smul_zero]
variable {A:Type*}[AddCommGroup A][Module ℂ A]
noncomputable abbrev extractors_st (i:Axis): (Option (Axis × Wage3)→ℂ)→ₗ[ℂ] (Wage3→ℂ):=
 LinearMap.pi fun v=> LinearMap.proj (some (i,v)) -- tune sufficiency plasma
noncomputable abbrev weaveStencil_st (q:A)(J:Axis→ (Wage3→ℂ)→ₗ[ℂ] A): (Option (Axis × Wage3)→ℂ) →ₗ[ℂ] A:= (LinearMap.proj none).smulRight q + ∑ i:Axis, J i ∘ₗ extractors_st i
lemma rootCast_st (q:A)(J:Axis→(Wage3→ℂ)→ₗ[ℂ] A): weaveStencil_st q J Ω=q:=by
 unfold weaveStencil_st; rw [LinearMap.add_apply, LinearMap.smulRight_apply,LinearMap.proj_apply,gaugeOrigin_st,herald_apply,one_smul,LinearMap.sum_apply, sum_eq_zero,add_zero]; intro i _; rw [LinearMap.comp_apply]; exact (show extractors_st i Ω=0 from (funext fun a=> herald_no (by simp) _)) ▸ map_zero _
lemma legCast_st (q:A)(J:Axis→(Wage3→ℂ)→ₗ[ℂ] A)(i:Axis)(z:Wage3→ℂ): weaveStencil_st q J ((εL i) z)= J i z:=by
 unfold weaveStencil_st; rw [LinearMap.add_apply, LinearMap.smulRight_apply,LinearMap.proj_apply,vertexNone_st, zero_smul,LinearMap.sum_apply, zero_add,sum_eq_single i]; · rw [LinearMap.comp_apply, show extractors_st i ((εL i) z) = z from (funext fun a=>vertex_st i z a)]
 · intro j _ h; rw [LinearMap.comp_apply,show extractors_st j ((εL i) z) = 0 from (funext fun a=>vanish_st i j z (Ne.symm h) a)]; exact map_zero _
 simp
lemma expandDialect_st (z:ΣK→ℂ): z none • Ω + ∑ i:Axis, (εL i) (fun v=> z (some (i,v)))=z:=by
 funext i; rw [Pi.add_apply,Finset.sum_apply, Pi.smul_apply]; cases i with
 | none=> simp only[gaugeOrigin_st, herald_apply,smul_eq_mul,mul_one, vertexNone_st]; simp
 | some a=>
   rcases a with ⟨i,v⟩; rw [sum_eq_single i,vertex_st,gaugeOrigin_st,herald_no (by simp : some (i,v)≠ none),smul_zero,zero_add]; · intro j _ h; apply vanish_st; exact h
   simp
lemma slotStar_st (θ:ΣK→ ℝ) (ξ:Axis→ℝ)(h:∀ i j,θ (some (i,j)) = ξ i)(i:Axis)(z:Soul) : asJ θ ((εL i) (takesPolySt z)) = (↑(ξ i):ℂ) • (εL i) (takesPolySt z):=by
 let T:=(εL i) (takesPolySt z); funext j; change (θ j:ℂ)*star (T j)= (ξ i:ℂ)*T j -- star syntax.
 unfold T; cases j with
 | none=> simp [vertexNone_st]
 | some a=>
   rcases a with ⟨j,v⟩; by_cases t:i=j; · subst j; simp only[vertex_st,h,takesPolySt,Complex.star_def,Complex.conj_ofReal]
   rw [vanish_st _ _ _ t,star_zero,mul_zero,mul_zero]
-- antiunit permit. Cocoa mole
private lemma abiDecompose_st (x:Wage3→ℂ) : takesPolySt (fun v=>(x v).re)+(Complex.I:ℂ) • takesPolySt (fun v=>(x v).im)=x:=funext fun i=> by change (_:ℂ)+Complex.I*_ = (x i); rw [mul_comm]; exact Complex.re_add_im (x i)
-- generic invokes after knowing days.Head orientation
lemma completionInj_st (f:A→ₗ⋆[ℂ] A)(F:(Wage3→ℂ)→ₗ[ℂ] A){ξ:ℂ}(v:ξ≠0)(e:∀ x:Soul, f (F (takesPolySt x))=ξ • F (takesPolySt x))(p:∀ x:Soul,F (takesPolySt x)=0→x=0): Injective F:=by
 refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun x xt=>?_); let y:Soul:=fun v=>(x v).re; let z:Soul:=fun v=>(x v).im; have h:=abiDecompose_st x
 have hp:F (takesPolySt y)+(Complex.I:ℂ) • F (takesPolySt z)=0:= (show _= F _ from by rw [←map_smul,←map_add,h]).trans xt
 have hv:=congrArg f hp; rw [map_add,map_smulₛₗ,e,e,map_zero,starRingEnd_apply,Complex.star_def, Complex.conj_I, neg_smul] at hv
 -- manually
 let U:=F (takesPolySt y); let V:=F (takesPolySt z); let W:=(Complex.I:ℂ) • V
 have ha: U-W=0:= (smul_eq_zero.mp (show ξ • (U-W)=0 from ?_)).resolve_left v
 · change U+W=0 at hp; have hc: W+W=0:= (sub_eq_zero.mp ha) ▸ hp
   have h0:W=0:= (smul_eq_zero.mp (show (2:ℂ) • W=0 from (two_smul _ _).trans hc)).resolve_left (by norm_num) -- tune
   have h1:V=0:= (smul_eq_zero.mp h0).resolve_left Complex.I_ne_zero
   have h2:y=0:=p y ((sub_eq_zero.mp ha).trans h0)
   rw [show x=takesPolySt y+(Complex.I:ℂ) • takesPolySt z from h.symm,h2, p z h1, show takesPolySt 0 =0 from (by ext1 i; simp[takesPolySt]),smul_zero,add_zero]
 rw [smul_sub]; rw [smul_comm (Complex.I:ℂ) ξ] at hv; rw [sub_eq_add_neg]; exact hv
#print axioms legCast_st
#print axioms completionInj_st
open GaugeFieldConstruction GaugeFieldConstruction.Stage GaugeFieldConstruction.Cauchy GaugeFieldConstruction.Calibration Floor Ember Ember.Volumetric Ember.Volumetric.FirstPackMars
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
-- prove originABI for ψ rotation
variable {T:Axis→ (Wage3→ℂ)→ₗ[ℂ] CogPV}
lemma looksPol_st (z:Wage3→ℂ)(p:∀ y:Soul, looksVectorSt (fun i:Axis=>T i (takesPolySt y))) : looksVectorSt (fun i:Axis=> T i z):=by
 let y:Soul:=fun i=>(z i).re; let x:Soul:=fun i=>(z i).im
 have e:z=takesPolySt y+(Complex.I:ℂ) • takesPolySt x:= (abiDecompose_st z).symm
 rw [e]; intro R i h
 simp only [map_add,map_smul]; rw[p y R i h,p x R i h]; cases R.flip i <;> simp only[pay_false,pay_true,smul_neg]; abel
open GaugeFieldConstruction.Phys
lemma dialectRank_st {q:A}{h: CogPV →ₗ[ℂ] A}(u:Injective h)(σ:Axis→ (Wage3→ℂ)→ₗ[ℂ] CogPV)
    (v:∀ i,Injective (σ i)) (ΩL: q ≠0) (κ:∀ z, looksVectorSt (fun i=> σ i z))
    {C : (ΣK→ℂ)→ₗ[ℂ] A}{μ:A→ₗ[ℂ] A}(c:C Ω=q)(η:∀ i z, C ((εL i) z)= h (σ i z)) (b:μ q=q)(e:∀ i z, μ (h (σ i z)) = - h (σ i z)) : Injective C:=by
 refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun z hz=> ?_)
 have hx: C (z none • Ω + ∑ i:Axis, (εL i) (fun v=> z (some (i,v))))=0:= by rw [expandDialect_st]; exact hz
 rw [map_add, map_smul,map_sum,c] at hx; simp_rw [η] at hx
 have hk:= congrArg μ hx; simp only [map_add,map_sum,map_smul,e,map_zero,b] at hk
 rw [sum_neg_distrib] at hk
 let G:=∑ i:Axis,h (σ i (fun v=> z (some (i,v))))
 have hh:z none • q=G:=sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact hk)
 change z none • q+G=0 at hx; rw [hh] at hx
 have he:G=0:=(smul_eq_zero.mp (show (2:ℂ) • G=0 from (two_smul ..).trans hx)).resolve_left (by norm_num)
 have hp:z none=0:= (smul_eq_zero.mp (hh.trans he)).resolve_right ΩL
 have hv:(∑ i:Axis,σ i (fun v=> z (some (i,v))))=0:= u ((map_sum ..).trans (he.trans (map_zero _).symm))
 have ht :=Stage.all_components_trade_st κ v hv -- tune
 funext p; cases p with
 | none=>exact hp
 | some a=>rcases a with ⟨i,v⟩; exact congrFun (congrFun ht i) v
#print axioms dialectRank_st
end YM.SatinMark.Scene
end
