import YM.CF.Cour.Lake
import YM.CF.Pec.Frond
import YM.CF.Skye.Hark
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Cour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Laic Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker
variable {B L:Side}{n k:ℕ}{e t x u C A:ℝ}
section
open scoped Matrix.Norms.Frobenius
lemma sleek (k:ℕ):∃ A:ℝ,0≤A∧∀ {m n:Side}{T:RG.StepData (More m) (More n)}(F:Forest T.ratio)(x:Snap F), ‖x‖ ≤1 → EnvM k (fine SU.group F) x A ∧ EnvM k (outer SU.group F) x A:=by
 obtain ⟨C,H⟩:=paint_supply group k; let U:=fineCost group k C; let V:= outerCost group k C; let Q:= max U V; refine ⟨Q, le_max_of_le_right (outer_pos _ _ H.1|>.le),fun F x hx=> ⟨⟨fun i=> ((fine_supply F H).2.2 _ _ hx).mono (le_max_left ..)⟩,⟨fun i=>((outer_supply F H).2.2 _ _ hx).mono (le_max_right ..)⟩⟩⟩
end
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
lemma gleanA(k:ℕ): ∃ q:ℝ,1≤q∧∀ {M n:Side}{T:RG.StepData (More M) (More n)}(F:Forest T.ratio)(x: Snap F),‖x‖≤1→ Jet.TransK k (fine SU.group F) x q ∧ Jet.TransK k (outer SU.group F) x q:=by
 obtain ⟨c,h,H⟩:= sleek k; have he:=dGray_pos h; let X:= (coordL (k:=SU.F)).symm.toContinuousLinearMap; let A:= ‖X‖* dGray c
 have ht {Y:Side}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ Bkg Y)(x:E)(u:EnvM k U x c): Jet.TransK k U x (max A 1):=by
    intro i; have hp: Allows k (fun y=>fund (U y i)) x A:= (Push.Uniform.allows_pi he fun m:SU.F=> Push.Uniform.allows_pi he fun n:SU.F=> delight U u i m n).linear X le_rfl; exact (⟨hp.analytic.of_le le_top,hp.norm_le⟩:Jet.Allows k _ _ A).mono (le_max_left ..)
 exact ⟨_,le_max_right ..,fun F x hx=>⟨ht _ _ (H F x hx).1,ht _ _ (H F x hx).2⟩⟩
lemma land_u (a:ℝ)(p:0<a):∃ u:ℝ,0<u ∧ ∀ x:E, ‖fund x-1‖ < u → ‖brand x-1‖≤a:=by
 let h:= fund_cont.isClosedEmbedding (show Function.Injective fund from SU.group.mat_injective) -- topology?
 have ht: ({x:E | ‖brand x-1‖ ≤ a}:Set E)∈𝓝 1:= (spinD.continuousAt.preimage_mem_nhds (t:={x| ‖x-1‖≤a}) (by rw [brand_one]; exact Filter.mem_of_superset (closedBall_mem_nhds (1:Twig) p) (fun i p=>mem_closedBall_iff_norm.mp p))) -- parser
 rw [h.isInducing.nhds_eq_comap] at ht; obtain ⟨v,g,V⟩:= ht; rw [fund_one] at g; obtain ⟨u,hu,hU⟩:=Metric.mem_nhds_iff.mp g; exact ⟨u,hu,fun x hx=> V (hU (mem_ball_iff_norm.mpr hx))⟩
lemma windA (L:Side)(p:0<e)(hk:1≤k)(hQ:1≤ C):∃ v:ℝ,0<v ∧ v≤1∧∀{M N:Side}{T:RG.StepData (More M) (More N)}(G:Ratio M N) (F:Forest T.ratio), G.count=L→(∀ x:Snap F,‖x‖≤v→Jet.TransK k (fine SU.group F) x C ∧ Jet.TransK k (outer SU.group F) x C)→ ∀ x:Snap F,‖x‖<v→ JointB G (hats F x) e:=by
 let s:= (L.val:ℝ)+8; let a:=e/s; have hs:0<s:=by unfold s; positivity
 obtain ⟨u,h,hU⟩:=land_u a (div_pos p hs); have hC:0<C:=zero_lt_one.trans_le hQ; let r:=min (u/C) 1; have hr:0<r:=lt_min (div_pos h hC) zero_lt_one
 have ha:e=s*a:=by unfold a; field_simp
 refine ⟨r,hr,min_le_right ..,?_⟩; intro M N T G F hm H x hx
 have ht{b:Side}(Y:Snap F→Bkg b)(p:Y 0=1)(he:∀ v:Snap F,‖v‖≤r→ Jet.TransK k Y v C)(i:Edge (Site b)):‖brand (Y x i)-1‖ ≤ a:=by
    apply hU; let f(j:Snap F):=fund (Y j i); have hg: f 0=1:=by simp [f,p,fund_one]
    have hh : ‖f x-1‖≤ C*‖x‖:=by
       rw [← hg]; let w:= ball (0:Snap F) r
       have hL(y)(hy:y∈w):Jet.Allows k f y C:=he _ (mem_ball_zero_iff.mp hy).le i
       have hm:= (convex_ball (0:Snap F) r).norm_image_sub_le_of_norm_fderiv_le (fun y hy=> ((hL _ hy).smooth.differentiableAt (by exact_mod_cast (show k≠0 by omega)))) (fun y hy=> Vol.drops2 (hL _ hy) hk) (mem_ball_self hr) (mem_ball_zero_iff.mpr hx)
       simpa only [sub_zero] using hm
    exact hh.trans_lt ((mul_comm C _).trans_lt ((lt_div_iff₀ hC).mp (hx.trans_le (min_le_left ..))))
 have hh(i): ‖brand ((hats F x).1 i)-brand ((1:Bkg (More N)) i)‖ ≤ a:=by rw [Pi.one_apply,brand_one]; exact ht (fine _ F) (congrArg Prod.fst hats0) (fun x hx=>(H x hx).1) _ -- Skin wrong
 have ht'(i): ‖brand ((hats F x).2 i)-brand ((1:Bkg (More M)) i)‖ ≤ a:=by rw [Pi.one_apply,brand_one]; exact ht (outer _ F) (congrArg Prod.snd hats0) (fun x hx=>(H x hx).2) _
 have hv:0+4*a≤e:=by unfold s at ha; have hp:0<a:=div_pos p hs; nlinarith only [ha,Nat.cast_nonneg L.val (α:=ℝ),hp]
 refine ⟨ (Skye.turns_B _ _ (guard0 (le_refl 0)) hh).shrink hv,(Skye.turns_B _ _ (guard0 (le_refl 0)) ht').shrink hv,fun i=>?_⟩
 have hw:= Skye.bumps _ _ hh ((ratio G).embed i.1) (pathL G i.2); rw [show travel (1:Bkg (More N)) ((ratio G).embed i.1) (pathL G i.2)=1 from ?_,brand_one,pathGL,hm] at hw
 · change ‖brand ((hats F x).2 i)-brand (travel _ _ _)‖ ≤ _; apply (norm_sub_le_norm_sub_add_norm_sub _ (1:Twig) _).trans; rw [norm_sub_rev 1]; apply (add_le_add (ht (outer _ F) (congrArg Prod.snd hats0) (fun x hx=>(H x hx).2) i) hw).trans; unfold s at ha; have hp:0<a:=div_pos p hs; linarith only [ha,hp]
 have he(W:Walk)(x:Site (More N)):travel (1:Bkg (More N)) x W=1:=by induction W generalizing x <;> simp [travel,Step.read, *]
 exact he _ _
end YM.CF.Cour
