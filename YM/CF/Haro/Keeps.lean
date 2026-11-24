import YM.CF.Haro.Wisp
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Haro
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
variable {c f:Side}(G:Ratio c f)(h: Odd G.count.val)
open Branch Laic
variable {t:ℝ}(p:0<t)(Y: cro G t)(W: Meter TailB G t)
open Skye Precision
open Jet Scree
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{z:E}{n:ℕ}{K u v w A' B' C':ℝ}
lemma norY {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F](A:E→F)(h:Allows n A z u):Allows n (-A) z u:=⟨h.smooth.neg,fun i p=>by change ‖iteratedFDeriv ℝ i (-A) z‖ ≤_; rw [iteratedFDeriv_neg_apply,norm_neg]; exact h.norm_le i p⟩
variable (X:Hub f){P:RG.BudgetPoint}{u' v':ℝ}(F:InkD f)(hp:PressB P X F u' v')(U:E→Pane f)(V:E→ Pane c)
variable (A B: Support (More f))(r s:Prism.Rock f)(i j:Prism.Rock c)(Z:E→Rill.Arch G t)(T:Rill.Arch G t)
variable (C Q:Toll (Iota G))(a:Suite (badge _) (pinH G t true) (pinH G t false) A C (W (true,true) A))(b:Suite (badge _) (pinH G t true) (pinH G t false) B Q (W (true,false) B))
-- path error paid.H.Var slots
abbrev θ_I(n:ℕ)(X Y U:ℝ):ℝ:=3*wheel_l n*(3*wheel_l n*(pole*X)*Y)*U
include p a b hp
lemma photon(g:Seat c→SU.E)(ξ:verQ G T)(L:Risk n (fun x=>fyL G true W (bring p (herb G (g ∘ (ratio G).parent) (Z x))) A r i) (fyL G true W (bring p T) A r i) z u v)
 (J:Risk n (fun x=>fyL G false W (bring p (herb G (g ∘ (ratio G).parent) (Z x))) B s j) (fyL G false W (bring p T) B s j) z u w)
 (E':Risk n (fun x=> CharM F r s (Lattice.gauge (g ∘ (ratio G).parent) (U x))) (CharM F r s 1) z u C') (hT:Allows n (fun x=>mater (travel (gauge g (V x)) (node i.1) (shiftH (node i.1) (node j.1)))-1) z u)(ht:u≤1): ∀ x y:Slot, Allows n (fun t=> (lyric G p W F A B r s i j (U t) (Z t)- taxi (V t) i j (lyric G p W F A B r s i j 1 T)) x y) z ((1+wheel_l n)* θ_I n v C' w*u):=by
 let I:=g ∘ (ratio G).parent; let T':=lyric G p W F A B r s i j 1 T
 let Kx(t:E):= lyric G p W F A B r s i j (gauge I (U t)) (herb G I (Z t))
 let Y:=fun t=>taxi (gauge g (V t)) i j T'; let R: Risk n Kx T' z u (θ_I n v C' w):= roam_p _ _ _ _ (roam_p _ _ _ _ (reS _ _ L) E' ht) J ht
 let P':=θ_I n v C' w; let v₁:=Kx-fun _=>T'; let W'(t:E):Op Slot:= mater (travel (gauge g (V t)) (node i.1) (shiftH (node i.1) (node j.1)))-1; let v₂:= (fun _ : E=>T')*W'
 have he:Allows n v₂ z (wheel_l n*P'*u):= leaf_h _ _ (allows_const _ R.1) hT
 have hx: v₁-v₂= Kx-Y:= by ext1 t; unfold v₁ v₂; change Kx t - T' - T'*(_-1)=_; rw [mul_sub,mul_one]; change _= Kx t - T'*_; abel
 have hy:Allows n (Kx-Y) z ((1+wheel_l n)* θ_I n v C' w*u):=by rw [←hx,sub_eq_add_neg]; apply (R.2.add (norY _ he)).mono (le_of_eq (by unfold P'; ring))
 let D:=putX g i; let L':=putX g j; have hd: D ∈ unitary (Op Slot):=(matter _).property; have hh:L'∈unitary (Op Slot):=(matter _).property; let f(t):= lyric G p W F A B r s i j (U t) (Z t)
 have hv': ∀ t, Kx t=D*f t*star L':=fun t=>by unfold Kx; rw [lyric_g G p W X F hp _ A B r s i j _ C Q a b I,show Peaks.scaleG G I=g from funext fun i=>by simp [I,Peaks.scaleG, Ratio.embed_parent]]
 intro x y; have hv: (fun t:E=> star D * (Kx-Y) t * L')=fun t=> f t-taxi (V t) i j T':=by
    ext1 u; rw [Pi.sub_apply]; rw [hv' u, show Y u = D* taxi (V u) i j T'*star L' from care i j (V u) T' (fun t=> taxing G p W X F hp A B r s i j T C Q a b t ξ) g]; rw [← sub_mul,← mul_sub, ← mul_assoc,←mul_assoc,hd.1,one_mul,mul_assoc, hh.1,mul_one] -- tune
 have he:=ship_x D L' hd hh _ hy; rw [hv] at he; exact cape_l _ he x y
omit a b hp
abbrev paintL (x:Prism.Rock f)(a:Prism.Rock c)(S:Toll (Iota G)):ℝ:= ∑ i:Slot,∑ j:Slot, S ((switchG G).symm (x,i)) (patchQ G (a,j))
lemma ship_r (τ:Bool)(p':Suite (badge _) (pinH G t true) (pinH G t false) A C (W (true,τ) A))(hv:0 ≤ v) (he:∀ x y, Allows n (fun s:E=> W (true,τ) A (bring p (Z s)) x y-W (true,τ) A (bring p T) x y) z (C x y*v)) : Risk n (fun s=> fyL G τ W (bring p (Z s)) A r i) (fyL G τ W (bring p T) A r i) z v (horn*paintL G r i C):=by
 let f(x y:Slot):= C ((switchG G).symm (r,x)) (patchQ G (i,y)); let Z':=paintL G r i C; have hf(x y):0≤f x y:=p'.nonn _ _; have ht(x y): f x y ≤ Z':=(single_le_sum (fun i _=>hf x i) (mem_univ y)).trans (single_le_sum (fun i _=>sum_nonneg (s:=univ) fun j _=>hf i j) (mem_univ _)); have hz:0 ≤ Z':=sum_nonneg (s:=univ) fun i _=>sum_nonneg (s:=univ) fun j _=>hf i j
 refine ⟨soft 1 _ hz (fun i j=> ((p'.expo ..).bounded _).trans (ht i j)),?_⟩ -- R `_`
 change Allows _ _ _ ((horn*Z')*v); rw [mul_assoc]; exact softL _ (mul_nonneg hz hv) _ (fun x y=>(he _ _).mono (mul_le_mul_of_nonneg_right (ht x y) hv))
end YM.CF.Haro
