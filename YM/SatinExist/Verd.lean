import YM.SatinExist.Regale
set_option autoImplicit false
set_option maxHeartbeats 330000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Mir.Trip Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology Kronecker
attribute [local instance] opCStarAlgebra
open Py.Rate.LocalLimit.Papal (Weaver household)
open YM.CF.Lamour YM.CF.Velvet YM.CF.Lamour.Bridge.Celeste
open Twah
namespace Chalice
/-! Adaptation of CFP SPF's uniform tangent proof. Now *matrices of generation*! also on-site hops, actual permit. -/
open Lamour.Bridge
open YM.Stationary (Gaia)
variable {I:Type} (Z:I→Stone)(O:ℕ→I → Cover)(L:List I) (D:I→Gaia)
open Py.Rate.LocalLimit.Papal (meanF)
variable (J:ℕ) (A:ℕ→ℕ)
variable (p:Tendsto A atTop atTop) (h: ∀ i, Tendsto (fun n:ℕ=>riseX (A n:ℝ) (O n i)) atTop (𝓝 (D i)))(v:∀ i j,D i=D j→ ∀ᶠ n in atTop,O n i=O n j)
-- uniform over N, not i. Estimate count later. setup.Glaze
local notation "M" i:max=> meanF (Chalice.wordsC Z (O i) L (A i)) (Chalice.depictionC Z L D)
private lemma lampC {N:Side}{T:Jill.Male}(k:Kea.Pad J N)(u:1≤ J)(x:Wave (Single N))(v:Sea (spar J T (1:Pane N)) x)(F:Weaver)(z:ℂ):alleyR (mateK N) x ((meanF F z) N (1,1))=alleyR (mateK _) x (F N (1,1))-z:=by rw [show meanF F z N (1,1) = F N (1,1)- z • (1: FC _) from rfl,map_sub,map_smul,alley_one u k x v,smul_eq_mul,mul_one]
include p h v
theorem fanC (ε:ℝ)(e:0<ε)(t:1≤ J):∀ᶠ n:ℕ in atTop, Clarity (meanF (wordsC Z (O n) L (A n)) (depictionC Z L D)) J ε:=by
 let K(i) (N:Side) (P:Jill.Male):Prop:= Py.Rate.LocalLimit.Papal.translucent (M i) J ε N P
 change ∀ᶠ i in atTop,∀ᶠ N:Side in atTop, Even N.val→∀ T:Jill.Male,K i N T
 by_contra z
 have hp:∃ᶠ i in atTop, A i>0 ∧ ∃ᶠ N:Side in atTop, ¬(Even N.val→∀ T:Jill.Male,K i N T):= ((not_eventually.mp z).and_eventually (p.eventually_gt_atTop 0)).mono (fun x h=> ⟨h.2, not_eventually.mp h.1⟩)
 have hk(i:ℕ):∃ j:ℕ,i ≤ j ∧ 0< A j ∧ (∃ (N:Side) (T:Jill.Male), Kea.Pad J N ∧ A j* Ember.pinch N ≤ (2:ℝ)⁻¹^i ∧ ¬ K j N T):=by
    obtain ⟨j,⟨hj,q⟩,f⟩:= (hp.and_eventually (eventually_ge_atTop i)).exists
    obtain ⟨k0,y⟩:= Glaze.pick_depth (p:=(show 0<(2:ℝ)⁻¹^i/(A j:ℝ) from (by positivity)))
    obtain ⟨N,pn,g,v⟩:= (q.and_eventually ((ownsHalo t).and (eventually_ge_atTop (⟨k0+1,by omega⟩:Side)))).exists
    push Not at pn; obtain ⟨w,T,X⟩:=pn; refine ⟨j,f,hj,N,T,(g w).1, (mul_comm _ _).le.trans ((le_div_iff₀ (by positivity : 0<(A j:ℝ))).1 (y (by change k0+1 ≤ N.val at v; omega))), X⟩
 choose C b c Ns M' k H X using hk
 have hq:Tendsto C atTop atTop:=tendsto_atTop_mono b tendsto_id
 let s:ℕ→ℕ:=A∘ C; let G:ℕ→I → Cover:= O∘C
 unfold K Py.Rate.LocalLimit.Papal.translucent at X; push Not at X; choose x u U using X
 have hy:Yard Ns (fun i=>(s i:ℝ)):= ⟨fun i=>by unfold s; dsimp; exact_mod_cast c i,tendsto_natCast_atTop_atTop.comp (p.comp hq),squeeze_zero (fun i=> by have hh:0<s i:= c i; exact mul_nonneg (by exact_mod_cast hh.le) (Ember.pinch_pos _).le) H (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)),fun i=>(k i).1⟩
 let T:= depictionC Z L D
 have hz (i): alleyR (mateK _) (x i) ((M (C i)) (Ns i) (1,1)) = alleyR (mateK _) (x i) (wordsC Z (O (C i)) L (A (C i)) _ (1,1))-T:=lampC J (k i) t (x i) (u i) _ _
 have hx:Tendsto (fun i=> alleyR (mateK (Ns i)) (x i) ((M (C i)) (Ns i) (1,1))) atTop (𝓝 0):=by
    have he:= tangentC' Z L s G D (fun i=>(h i).comp hq) (fun i j y=> hq.eventually (v i j y)) J hy t M' k x u; simp_rw [hz]; exact (by simpa only [T,G,s,Function.comp_apply,sub_self] using he.sub_const T) -- order
 obtain ⟨i,p'⟩:=(((tendsto_zero_iff_norm_tendsto_zero.mp hx).eventually (gt_mem_nhds e))).exists
 exact not_lt_of_ge ((U i).le) p'
end Chalice
end YM.CF.Buffered.Ballad
