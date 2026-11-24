import YM.CF.Hest.Cup
import YM.CF.Hest.Poet
import YM.CF.Hest.Vera
import YM.CF.Hest.Gust
import YM.CF.Hest.Foy
import YM.CF.Hest.Hull
import YM.CF.Facet.Prima
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.Hest
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Tenant Proa Broc Jet MeasureTheory Urn Levier Cour Facet
open scoped Matrix.Norms.L2Operator Topology BigOperators NNReal Classical ContDiff InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {ι:Type}{N P m X B L:Side}{n k j:ℕ}{e d t x u C A:ℝ}
open Newt Hors Souk
open RG Pressure Push AnalyticBridge.LocalGaussianLaws
local notation "GG"=>group
variable{T:Roam m X B}{c b a r w σ:ℝ}
variable{G:Ratio (CSide m B) (CSide X B)}{A:Haze m X B G e}{n:ℕ}{k':T.Choices}{U:nomA m X B→ Op (Single (CSide m B))}
section
variable {F:Forest T.ratio}{H:Tube GG T}{w' : Odd L.val}{P': Aim (CSide m B)}{J':Aim (CSide X B)}{D:Male}{Q:Pricing j L w' (Thread j)}{t': Vox m B→ AxisChart GG F}{K:Teller GG}{l:ℕ}{M α z:ℝ}
lemma tual {v:Mast GG (More (CSide m B))→ Op (Single (CSide m B))}(p:∀ i j,ContDiffAt ℝ (↑n) (fun k=> v k i j) 0): ContDiffAt ℝ n v 0:=by
 let V:= (Nacre.coordL (k:=Single (CSide m B))); let f:= V ∘ v; have hv:ContDiffAt ℝ n f 0:=contDiffAt_pi.mpr fun i=> contDiffAt_pi.mpr fun j=> p i j; exact (V.symm.contDiff.contDiffAt.comp (f:=f) _ hv).congr_of_eventuallyEq (Eventually.of_forall (fun k=> Eq.symm (V.symm_apply_apply _)))
abbrev portA (n:ℕ) :=univ.filter fun S:mSeal X B=>S.card≤ n
lemma xxxA (d:ℝ)(h:0<e)(I:Ind G A a b C n (Budget L w' J'.den P'.den G D j))(hq:Fleck G h F r C n)
 (K z: Mast GG (More (CSide m B))→Fish (Key F GG)) (hh:z=Uniform.station t') (ht:0<d) (hp:cFoot 3 (emergence L j w' G F t' D J'.den-flareP L j w' D P'.den)) (hv:3 ≤ n)(hy:0<a)
 (hk:1 ≤ w) (H:∀ y: Mast GG (More (CSide m B)),‖y‖<1→ Allows 2 (fun u=>K (d • u)) y (w*d)∧Allows 2 (fun u=>z (d • u)) y (w*d)) (he:3*w*d<r)(hF:3*w*d≤1)(hΛ: Allows 2 (fun v:Mast GG (More (CSide m B))=>K (d • v)- z (d • v)) 0 M) (o p:Single (CSide m B))(k:ℕ): let U(v:Mast GG (More (CSide m B))):=∑ i∈ portA k,A i (frameT G h F (flute F K d v)) o p
 Jet.Allows 2 U 0 (2^2*Jet.composeCost 2 b 1*M+Jet.composeCost 2 (Real.exp (-a*k)*b) 1):=by
 intro U
 let X₁:=flute F K d; let Z:=flute F z d
 let D'(S:Finset (mSeal _ _))(i j:Single (CSide m B))(x):=∑ v∈ S,A v (frameT G h F x) i j
 have hQ{L:Finset (mSeal _ B)} (x: Snap F)(i j)(hk:‖x‖<r):Jet.Allows n (D' L i j) x b:=by
    have hx:= snick I h F hq L 0 i j hy (fun i _=>Nat.zero_le _) x hk; rw [Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] at hx; exact hx -- tune
 let V(s:Mast GG (More (CSide m B))):= ∑ i,A i (frameT G h F (Z s)); have hz(y)(hy:‖y‖<1):Jet.Allows 2 Z y (3*w*d):=(turn_safe (H y hy).1 (H y hy).2 ht.le hk hy 0 (Set.left_mem_Icc.mpr zero_le_one)).germ (Eventually.of_forall fun i=>by simp; rfl) -- tune Ux unused
 have hZ: ‖(0:Mast GG (More (CSide m B)))‖ <1:=by simp
 have hh': ContDiffAt ℝ (2:ℕ) V 0:=by
    apply tual; intro i j; have he':(fun y=> V y i j)=D' univ i j ∘ Z:=by ext1 u; unfold D' V; rw [Matrix.sum_apply]; rfl
    rw [he']; exact (((hQ _ i j ((hz 0 hZ).value.trans_lt he)).smooth).of_le (by exact_mod_cast (show 2≤n by omega))).comp _ ((hz 0 hZ).smooth)
 let V':= V; subst z; have hp':= voss d h I hh' hq (by filter_upwards [ball_mem_nhds _ zero_lt_one] with i hi; exact (hz _ (mem_ball_zero_iff.mp hi)).value.trans_lt he) ht hp
 let F':= (portA k : Finset (mSeal X B)); let g:= D' F' o p; let H':=D' F'ᶜ o p; let K':= H' ∘ Z; have hP: Jet.Allows 2 K' 0 (Jet.composeCost 2 (Real.exp (-a*k)* b) 1):=by
    have hp:= (snick I h F hq F'ᶜ k o p hy ?_ (Z 0) ((hz 0 hZ).value.trans_lt he)).order (show 2 ≤ n by omega); swap; · intro i hi; simp only [F',portA,mem_compl,mem_filter,mem_univ,true_and] at hi; omega
    exact hp.comp (f:=Z) ((hz 0 hZ).mono hF)
 let M':= g ∘ Z; let B':= M'+K'
 have hb: Jet.Allows 2 (U-M') 0 (2^2*Jet.composeCost 2 b 1*M):= varying (fun x hx=> (hQ (L:=F') x o p hx).order (by omega)) hZ H ht.le hk he hF hΛ -- may hide
 let S:=boc o p; have hω: V'=V:=rfl
 have ht:B'=S ∘ V:=by ext1 i; unfold Function.comp B' M' K'; change D' F' o p _ + D' F'ᶜ o p _= V i o p; unfold V D'; rw [Matrix.sum_apply,Finset.sum_add_sum_compl]
 have hζ : Jet.Allows 2 B' 0 0:=by
    rw [ht]; refine ⟨S.contDiff.contDiffAt.comp _ hh',fun i l=>?_⟩; rw [S.iteratedFDeriv_comp_left hh' (by exact_mod_cast l), show iteratedFDeriv ℝ i V 0=0 from hp' i (by omega), show S.compContinuousMultilinearMap _=0 from ContinuousMultilinearMap.ext (fun x=>by change S (0:Op _) =0; rw [map_zero]), norm_zero]
 have hγ:= subtract_p hζ hP; change Jet.Allows 2 (B'-K') 0 _ at hγ; rw [show B'-K'=M' from add_sub_cancel_right ..,zero_add] at hγ
 apply (hb.add hγ).germ; filter_upwards with i; change U i- M' i + M' i= _; rw [sub_add_cancel]
end
end YM.CF.Hest
