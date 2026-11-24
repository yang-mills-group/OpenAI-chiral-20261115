import YM.SatinExist.FoyerAction
import YM.SatinExist.Relume
import YM.SatinExist.Liber
import SatinThinFusionPaleness
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open _root_.YM.SatinExist Lancet
namespace Spine
/- analytic migration of price even on nonenclave
 pieces of Fars. not asserting operators or Pace on either. -/
abbrev PaysX (f:ℕ→ℂ):Prop:= ∃ g:ℂ→ℂ, Lancet.Full g ∧ ContinuousOn g {z:ℂ| 0 ≤ z.re} ∧ ∀ i:ℕ, f i=g i -- issue S.F at imaginary boundary not continuous? use real only
-- chosen brain, real continuity only
def ChargesX (f:ℕ→ℂ):Prop:=∃ (g:ℂ→ℂ)(p:ℝ→ℂ), Lancet.Full g ∧ Continuous p ∧ (∀ t:ℝ, 0<t→ g t=p t) ∧ ∀ i:ℕ,f i=p i
namespace ChargesX
variable {f h:ℕ→ℂ}
lemma add (u:ChargesX f)(v:ChargesX h): ChargesX (f+h):=by
 obtain ⟨g,p,a,b,c,d⟩:=u; obtain ⟨g',p',u,w,t,z⟩:=v; exact ⟨g+g',p+p',a.add u,b.add w,fun x a=> congrArg₂ (·+·) (c x a) (t x a),fun i=> congrArg₂ (·+·) (d i) (z i)⟩
lemma mul (u:ChargesX f)(v:ChargesX h): ChargesX (f*h):=by
 obtain ⟨g,p,a,b,c,d⟩:=u; obtain ⟨g',p',u,w,t,z⟩:=v; exact ⟨g*g',p*p',a.mul u,b.mul w,fun x a=> congrArg₂ (·*·) (c x a) (t x a),fun i=> congrArg₂ (·*·) (d i) (z i)⟩
lemma con(e:ℂ):ChargesX (fun _=>e):=⟨_,_,Lancet.Full.con e,continuous_const,fun _ _=>rfl,fun _=>rfl⟩
lemma sub (u:ChargesX f)(v:ChargesX h): ChargesX (f-h):=by
 convert u.add ((con (-1)).mul v) using 1; funext i; simp [sub_eq_add_neg]
lemma sum{I:Type*}{s:Finset I}(F:I→ℕ→ℂ)(u:∀ i∈s,ChargesX (F i)):ChargesX (fun k=>∑ i∈s,F i k):=by
 induction s using Finset.induction_on with
 | empty=> simp [con]
 | insert i s e ih=> refine (Eq.mp ?_ ((u _ (mem_insert_self ..)).add (ih fun j v=>u _ (mem_insert_of_mem v)))); exact congrArg ChargesX (funext fun j=>(sum_insert (f:=fun i=> F i j) e).symm)
lemma migrate (u:ChargesX f)(e:f 0 ≠0): ∃ᶠ n:ℕ in atTop,f n≠0:=by
 obtain ⟨g,p,⟨K,v,h⟩,b,k,r⟩:=u; have h':p 0≠0:=by rwa [r,Nat.cast_zero] at e
 obtain ⟨x,A,E⟩:= Filter.Eventually.exists (f:=𝓝[>] (0:ℝ)) ((show ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin).and (((b.tendsto 0).eventually (isOpen_ne.mem_nhds h')).filter_mono nhdsWithin_le_nhds))
 refine ((Lancet.cont_rail g K v h 1 x zero_lt_one A (by rw [k _ A]; exact E)).and_eventually (eventually_gt_atTop 0)).mono (fun i v=>?_); rw [r,← k i (by exact_mod_cast v.2)]; simpa using v.1
end ChargesX
variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)(s:ℕ)
local notation "K"=> P.calibration
local notation "Y"=> P.run
local notation "H"=> P.large
local notation "Φ"=> P.singleState 3 s x
local notation "χ"=> P.advocate 3 x j
local notation "Π"=> P.foyer x j
local notation "S₀"=> Selected.ride Y H P.law P.history P.projection.clipped j false (P.room j) (P.orientHouse x j)
open OS.Semigroup
private lemma priceX {HC:Hilbert} (G:OS.Semigroup HC j)(x y:HC.space)(p:ℝ)(q:0<p):ChargesX (fun n=>inner ℂ x (G.E (((n:ℝ)*p).toNNReal) y)):=by
 let f(z:ℂ):=inner ℂ x (G.F (z*p) y); let Υ(t:ℝ):= inner ℂ x (G.E ((t*p).toNNReal) y)
 have hz (z:ℂ)(h:0<z.re):0<(z*p).re:=by rw [Complex.mul_re,Complex.ofReal_im,mul_zero,sub_zero]; exact mul_pos h q
 have hf: Lancet.Full f:=by
    let g:= (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ HC.space y); refine ⟨‖x‖*‖y‖,by positivity,fun z b=>?_,fun z b=>?_⟩
    · let e : DifferentiableAt ℂ (fun z:ℂ => z*p) z:= differentiableAt_id.mul_const _
      exact (g.analyticAt _|>.differentiableAt.comp z ((G.localHeat _ (hz _ b)).differentiableAt.comp (f:=fun w:ℂ=> w*p) z e)).differentiableWithinAt
    exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (((G.F (z*p)).le_opNorm y).trans (mul_le_of_le_one_left (norm_nonneg _) (G.norm_row (hz z b)))) (norm_nonneg _))
 refine ⟨f,Υ,hf,continuous_const.inner ((G.continuousE _).comp (continuous_real_toNNReal.comp (continuous_id.mul_const p))),?_,fun n=>rfl⟩
 intro t v; unfold f Υ; rw [←G.roots_heat (Real.toNNReal_pos.mpr (mul_pos v q)),OS.Semigroup.duration,Real.coe_toNNReal _ (mul_pos v q).le]; push_cast <;> rfl -- tune
-- forward at stamp
variable (m:ℕ)(S T:Finset Cover)(f g:P.Test)
local notation "N"=> P.par
private lemma mountAX (c:ℕ)(A B:P.Vox j s):
 Φ (P.reflectTest j (P.voxTest j s A)*P.shifts j c (P.voxTest j s B))=inner ℂ ((Π) ((P.stateVox j χ s) A)) ((S₀).E (whenly (timeMesh N) s c) ((Π) ((P.stateVox j χ s) B))):=by
 rw [← P.high_wait x j c s s (le_refl _) B,← P.moves_p, LinearIsometryEquiv.inner_map_map,P.gram_at,P.halfMovesOf]
 rw [show (P.halfShift j ((↑(2*c:ℕ)):ℤ))=_ from (by rw [show (↑(2*c:ℕ):ℤ)=2*(c:ℤ) from (by exact_mod_cast rfl),P.halfDouble]:P.halfShift j ((↑(2*c:ℕ)):ℤ)=P.shifts j c)]
 exact Eq.symm (P.single_agrees ..) -- tune
open Six Aria Casting
variable {k:ℤ}{L V: Finset Axis}
lemma company (h:f∈bay K S true)(y:g∈bay K T true)(v:0 ≤ k)(p:Punctus (P:=P) false L k S)(r:Punctus (P:=P) true V k T)(Z:ℕ)(u:0<Z) : ChargesX (fun i:ℕ=> Φ (f*P.shifts j (Z*i:ℕ) g)):= by
 let B:= (P.positiveVox j s T g y (fun z x=>by have hp:= r z x j; simp only [ite_true] at hp; split at hp <;> omega)); let S':=reflectedBox j 0 S; let A:= P.positiveVox j s S' (P.reflectTest j f) (P.canFlip S j h) (fun z t=>by obtain ⟨w,g,t'⟩:= reflect_stays j 0 S t; rw [t',if_pos rfl]; have hp:=p w g j; simp only [Bool.false_eq_true,ite_false] at hp; split at hp<;> omega)
 let l:= mill (timeMesh P.par) s; let d:ℝ:=Z*(l:ℝ); have hg:0<d:=mul_pos (by positivity) (mill_pos ..)
 convert priceX j (S₀) ((Π) (P.stateVox j χ s A)) ((Π) (P.stateVox j χ s B)) d hg using 1; funext i
 have ht:= P.mountAX x j s (Z*i) A B; rw [show P.voxTest j s A=P.reflectTest j f from rfl, show _= f from (show P.reflectTest j (P.reflectTest j f)= f from aureoleTwice ..)] at ht
 have he: (((i:ℝ)*d).toNNReal)= whenly (timeMesh N) s (Z*i):= by ext; rw [Real.coe_toNNReal _ (mul_nonneg (by positivity) hg.le)]; unfold whenly d; push_cast; ring
 exact ht.trans (congrArg (fun t=> inner ℂ ((Π) _) ((S₀).E t _)) he.symm)
-- strictly supported abstract Dome marks, compare selected x forecast separately; not anticommuting charge. retain Cask letter registration.
private lemma spur (d:P.Test)(S:Finset Cover)(e:d∈bay K S true): ∃ G F:Evens S→ P.Test,(∀ i,PureMatter K (G i) ∧ G i∈bay K S true ∧ PureGauge K (F i) ∧ F i∈bay K S true) ∧ d=∑ i:Evens S,G i*F i:=by
 obtain ⟨u,rfl⟩:= accolade K S _ e
 let A(i:Evens S):= Sound.sing K (tagWord S i.val)
 have ht(i:Evens S):InTest K true S false (A i):=i.property ▸ sung K _ (Satin.brand S _)
 let B(i:Evens S):Dome K:= ⟨A i,broadCompile _ _ (ht i)⟩
 let G(i:Evens S): Dome K:=⟨scalar K (daub S (u i)), broadCompile K S (.seed (authentic ..))⟩
 refine ⟨B,G,fun i=>⟨wordIndependent K _, (Tapestry.locates ..).2 (ht i),⟨S,daub S (u i),authentic ..,rfl⟩,(Tapestry.locates ..).2 (show InTest K true S false (scalar K (daub S (u i))) from (.seed (authentic ..)))⟩,?_⟩
 simp_rw [mul_comm (B _)]; apply Subtype.ext; change render S K u=(screenHall K).val _; rw [render_eq,map_sum]; rfl
variable (D:P.Test→ₗ[ℂ]ℂ)
lemma costSplitX (X:Comparison K Φ D)(h:f∈bay K S true)(y:g∈bay K T true)(v:0 ≤ k)(p:Punctus (P:=P) false L k S)(r:Punctus (P:=P) true V k T)(Z:ℕ)(u:0<Z) : ChargesX (fun i:ℕ=> D (f*P.shifts j (Z*i:ℕ) g)):=by
 obtain ⟨G,F,g₁,g₂⟩:= P.spur f S h; obtain ⟨A,B,h₁,h₂⟩:= P.spur g T y
 let M:=(fun (i:Evens S) (t:Evens T) (x:ℕ)=> D (G i * F i * (P.shifts j (Z*x:ℕ) (A t*B t))))
 have hp : (fun i:ℕ=> D (f*P.shifts j (Z*i:ℕ) g)) = (fun z:ℕ=>∑ i:Evens S,∑ n:Evens T,M i n z):=by
    funext z; rw [g₂,h₂,map_sum, sum_mul]; simp_rw [mul_sum,map_sum]; rfl
 rw [hp]; apply ChargesX.sum; intro i _; apply ChargesX.sum; intro d _
 let S₁:= fun n:ℕ=> P.shifts j (Z*n:ℕ)
 let U(n:ℕ):=F i *S₁ n (B d); let V'(n:ℕ):=G i *S₁ n (A d)
 have hv(n:ℕ): PureMatter K (V' n):= matterPure_mul K (g₁ i).1 (P.copyIndependent j (h₁ d).1 _)
 have hz(n:ℕ): PureGauge K (U n):= gaugePure_mul K (g₁ i).2.2.1 (P.shifts_pure (B d) j _ (h₁ d).2.2.1)
 have Ht : M i d=(fun n=> Φ (U n)*Φ (V' n)) :=by
    funext n; unfold M; rw [map_mul (P.shifts j (Z*n:ℕ))]; change D (G i * F i*(S₁ n (A d)*S₁ n (B d)))=_; rw [show G i * F i * _=U n * V' n from ?_, X.factors (U n) (V' n) (hz n) (hv n),X.link _ (hz n), X.matter _ (hv n)]
    unfold U V'; ring
 rw [Ht]; exact (P.company x j s S T _ _ (g₁ i).2.2.2 (h₁ d).2.2.2 v p r Z u).mul (P.company x j s S T _ _ (g₁ i).2.1 (h₁ d).2.1 v p r Z u) -- tune `function` defeq
lemma stamp_comparison (y: Comparison K Φ D)(d:P.Test)(z:ℤ): D (P.shifts j z d)=D d:=by
 obtain ⟨S,e⟩:= findsBay K d; obtain ⟨F,B,h,rfl⟩:=P.spur d S e
 rw [map_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=>?_ ; let p:=(h i).1; let q:=(h i).2.2.1; let A:= P.shifts j z; have u:= P.shifts_pure _ j z q; have v:= P.copyIndependent j p z; rw [mul_comm (F i),map_mul,y.factors _ _ u v,y.factors _ _ q p, y.link _ u, y.matter _ v, y.link _ q, y.matter _ p,P.stamp_title,P.stamp_title]
#print axioms company
#print axioms costSplitX
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
