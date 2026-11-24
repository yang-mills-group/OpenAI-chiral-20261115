import YM.CF.Kennel.Ast
import YM.CF.Thera.Ticket
import YM.CF.Jet.Vista
set_option autoImplicit false
set_option synthInstance.maxSize 9000
noncomputable section
namespace YM.CF.Kennel
open Function Filter Lattice Wilson Laurent Precision Tree Finset Exterior Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N P n:Side}(G:Ratio N P)
lemma foot_l(e:ℝ)(g:Site (More P)→E)(X:Op (Single P)): foot G (ActZ g X)=twist ((parcel G true e).run g) (foot G X):=by unfold ActZ; rw [twist_formula,twist_formula]; change foot G _=foot G _*foot G X*star (foot G _); rw [←foot_mul,←foot_s,←foot_mul]
lemma summit_l(e:ℝ)(g:Site (More P)→E)(X:Op (Iota G)): summit (patchQ G) (twist ((parcel G false e).run g) X)=ActZ (scaleG G g) (summit (patchQ G) X):=by
 apply endorseI G; rw [spry, ActZ,twist_formula,twist_formula]; let V:=((parcel G false e).run g).val; let U:=(tradew N (scaleG G g)).val; let T:=hood G; have ⟨p,h⟩:=crest_pose G g e; change T*V=endorse G U at p
 change T*(V*X*star V)*T=_
 have hv: star T=T:=(hood_proj G).2
 have hh:star V*T=endorse G (star U):=by rw [← hv,←star_mul,p,endorse_star]
 have hk:T*T=T:=(hood_proj G).1
 change T*_*T=endorse G (U*summit (patchQ G) X*star U); calc
  _ = (T*V)*T*X*(T*(star V*T)):=by rw [show T*V*T=T*V by rw [p]; unfold T hood; rw [rude,mul_one],show T*(star V*T)=star V*T from (by rw [hh]; unfold T hood; rw [rude,one_mul])]; simp only [mul_assoc]
  _ = endorse G U*(T*X*T)*endorse G (star U):=by rw [p,hh]; simp only [mul_assoc]
  _ = _:=by unfold T; rw [← spry,rude,rude]
lemma crown_air {S:Set (Coil N P)}{H:Type}[Group H]{V:Type}[Fintype V][DecidableEq V]{J:Stage V (Iota G) (↥S) H}{B A:Branch.Tag J}{a b:ℝ}{F:Coil N P→Op (Iota G)}(h:Crown (badge _) A B a b (fun i=> F i.val))(x:Coil N P)(ht:S∈𝓝 x): ContDiffAt ℝ ω F x:=by
 apply Nacre.tort.mpr; intro i j; have hh : Looks S (fun p=> F p.val i j) := h.air i j
 let U(p:↥S):= F p.val i j; have hu:Continuous U:=by
   obtain ⟨M,C,h,e,hx⟩:=h; have hm: Continuous (fun p:↥S=> F p.val):=by simp_rw [hx]; exact continuous_finsetSum _ fun i _=>(h i).toTicket.cont
   exact hm.matrix_elem i j
 have hk:=(Jet.interiorC hh hu _ ht).restrictScalars (𝕜:=ℝ) -- tune
 apply hk.contDiffAt.congr_of_eventuallyEq; filter_upwards [ht] with y hy; exact Eq.symm (dif_pos hy)
lemma crown_pulse {a b d:ℝ}{B A:Bool}{F:Coil N P→Op (Iota G)}(h:Crown (badge _) (parcel G B d) (parcel G A d) a b (fun i=> F i.val))(x:Nom N P)(hp: unionP x∈legal G d)(g:Site (More P)→ E): F (unionP (july G g x))= ((parcel G B d).run g).val*F (unionP x)*star ((parcel G A d).run g).val:=by
 rw [jig]; exact h.lib.tiesK.frame g (⟨unionP x,hp⟩:legal G d)
lemma near_g (a:ℝ)(p:0<a):∀ᶠ x:Bkg n in 𝓝 1, Guard x a:=by
 have he (x:Site n)(i j:Axis): ∀ᶠ v:Bkg n in 𝓝 1, ‖brand (travel v x (square i j))-1‖<a :=by
   let f(V:Bkg n):=brand (travel V x (square i j)); have hv:f 1=1:=by simp [f, travel,square,brand_one]
   have hh :Tendsto f (𝓝 1) (𝓝 1):=hv ▸ (spinD.comp (travel_cont ..)).tendsto (1:Bkg n)
   simpa only [hv,sub_self,norm_zero] using ((hh.sub_const 1).norm.eventually (gt_mem_nhds (show ‖(1:Twig)-1‖<a from by simpa using p))) -- tune
 filter_upwards [eventually_all.mpr fun x=> eventually_all.mpr fun i=> eventually_all.mpr (he x i)] with x h
 refine ⟨fun i j k _=> (norm_snd_le _).trans (h i j k).le, fun i j k _=> (norm_fst_le _).trans (h i j k).le⟩
lemma near_j (a:ℝ)(p:0<a):∀ᶠ x:Nom N P in 𝓝 1, JointB G x a:=by
 let T(i:Guy (N:=N))(x:Nom N P):=brand (x.2 i)-brand (travel x.1 ((ratio G).embed i.1) (pathL G i.2)); have hp(i): T i 1=0:=by
   unfold T; simp only [Prod.snd_one,Pi.one_apply,Prod.fst_one]; rw [show travel (1:Bkg (More P)) _ _=1 from ?_,sub_self]; simpa only [link_one] using (Push.stroll_zero (G:=group) (pathL G i.2) ((ratio G).embed i.1))
 have hx(i):Continuous (T i):=(spinD.comp ((continuous_apply i).comp continuous_snd)).sub (spinD.comp ((travel_cont ..).comp continuous_fst)); have ht(i):∀ᶠ x:Nom N P in 𝓝 1,‖T i x‖<a:= (hx i|>.norm|>.tendsto (1:Nom N P)).eventually (gt_mem_nhds (show ‖T i 1‖ <a by rwa [hp,norm_zero]))
 filter_upwards [ (continuous_fst.tendsto (1:Nom N P)).eventually (near_g a p), (continuous_snd.tendsto (1:Nom N P)).eventually (near_g a p), eventually_all.mpr ht] with x hx hy ht; exact ⟨hx,hy,fun i=>(ht i).le⟩
end YM.CF.Kennel
