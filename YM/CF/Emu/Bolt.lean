import YM.CF.Emu.Fern
set_option autoImplicit false
noncomputable section
namespace YM.CF.Emu
open YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Kea Flare Rush Tulip Cube Fock SU Dial Thera
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open YM.Stationary (Gaia)
variable {N:Side}{j:ℕ}{M:Jill.Male}{R C r:ℝ}{d:Candle}
def skinF(a:Wing)(x:Slot):Wing:= ⟨a.a,x,a.ord⟩
lemma hen(o:Site N)(z:Cover)(a:Wing)(U:Bkg (More N))(t:E): hint o z a U t= ∑ i:Slot, (matter t).val i a.x • hint o z (skinF a i) U 1:=by
 have hp:stemF o z a U t=stemF o z a U 1*t:=by unfold stemF; rw [mul_one]
 unfold hint; rw [hp,map_mul,cue,act_mul,tint,map_sum,Finset.smul_sum]; apply sum_congr rfl; intro i _; rw [map_smul,smul_comm]; rfl
-- full band arbitrary moving h rotations.
variable {s:ℕ→Side}{L:ℕ→ℝ}
def hopF(o:Site N)(x y:Cover)(a b:Wing)(U:Bkg (More N))(t:E)(A:Op (Single N))(R:ℝ):= (R:ℂ)^3*inner ℂ (hint o x a U t) (acts A (hint o y b U t))
def frank(a b:Wing)(p:Gaia):= if a.x=b.x then pencil p a.a b.a else 0
lemma givex(o:Site N)(x y:Cover)(a b:Wing)(U:Bkg (More N))(t:E)(A:Op (Single N))(R:ℝ)(p:Gaia) : let c(i j:Slot):=star ((matter t).val i a.x)*(matter t).val j b.x; let f a b:= hopF o x y a b U t A R; let h a b:= hopF o x y a b U 1 A R;
     f a b-frank a b p= ∑ i,∑ j,c i j* (h (skinF a i) (skinF b j)-frank (skinF a i) (skinF b j) p):=by
 intro c f h
 simp_rw [mul_sub,sum_sub_distrib]; congr 1
 · unfold f hopF; rw [hen _ _ a, hen _ _ b, sum_inner]; simp_rw [map_sum,inner_sum,map_smul,mul_sum]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; rw [inner_smul_left,inner_smul_right]; unfold c h hopF; simp only [starRingEnd_apply]; ring
 let V:= matter t; have hp : ∑ i:Slot,c i i = (1:Op Slot) a.x b.x:=by
    rw [← show star V.val*V.val=1 from V.property.1, Matrix.mul_apply]; exact sum_congr rfl fun i _=>rfl
 unfold frank; change _=∑ i,∑ j,c i j*(if i=j then pencil p a.a b.a else 0)
 simp_rw [mul_ite,mul_zero, sum_ite_eq,mem_univ,ite_true]; rw [← sum_mul,hp,Matrix.one_apply]; split_ifs with v; simp; simp
-- small perturb weighted
lemma bendV {f g:ℕ→ℂ}(h:Tendsto f atTop (𝓝 0))(u:∀ᶠ i in atTop,‖g i‖≤1): Tendsto (fun i=>g i*f i) atTop (𝓝 0):=by
 rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢; refine squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) ?_ h; exact u.mono (fun i p=>by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) p)
lemma tally {d:ℕ→Candle}(S:∀ i,Slide (s i) (d i))(W:ℕ→Jill.Male)(F:∀ i,Stag (s i)→ Peb)(o:∀ i,Site (s i))(k:Yard s L)(p:0<r)(g:0<C)(A:∀ x:Slot,∀ᶠ i in atTop, FormU ((S i).u x) j (W i) r C (trackF (S i) (F i) x))(a b:Wing)(x y:ℕ→Cover)(u: Gaia)(e:u≠0∨(u=0∧ ∀ᶠ i in atTop,x i=y i))(w:Tendsto (fun i=>riseX (L i) (x i-y i)) atTop (𝓝 u))(h:1 ≤ j)(T:ℕ→E): Tendsto (fun i=>hopF (o i) (x i) (y i) a b (Kea.tax (d i)) (T i) (Dofu (s i) (F i)) (L i)) atTop (𝓝 (frank a b u)):=by
 let V(i)(t:E)(a b:Wing):= hopF (o i) (x i) (y i) a b (Kea.tax (d i)) t (Dofu (s i) (F i)) (L i)
 have hz(a b:Wing): Tendsto (fun i=>V i 1 a b) atTop (𝓝 (frank a b u)):=by
    unfold V hopF; simp_rw [show ∀ i,(L i:ℂ)^3*inner ℂ (hint (o i) (x i) a (Kea.tax (d i)) 1) (acts (Dofu (s i) (F i)) (hint (o i) (y i) b (Kea.tax (d i)) 1))= _ from fun i=> mist (S i) _ _ _ _ _ (F i) _]; unfold frank; split_ifs; swap; exact tendsto_const_nhds
    have ht : Tendsto (fun i=>bore ((S i).u a.x) (L i) (x i-y i) (trackF (S i) (F i) a.x)) atTop (𝓝 (pencil u)):=by
       rcases e with e|⟨rfl,he⟩; exact k.struck (A _) h e w p g
       rw [show pencil 0=0 from (by simp [pencil])]; exact (k.sol h p g _ _ _ (A a.x)).congr' (he.mono fun i e=>by change _=bore _ _ (x i-y i) _; rw [e,sub_self])
    refine (show Continuous fun p:Peb=> p a.a b.a from ?_).continuousAt.tendsto.comp ht -- known
    exact continuous_id.matrix_elem a.a b.a
 suffices hh:Tendsto (fun i=>V i (T i) a b-frank a b u) atTop (𝓝 0) by simpa only [sub_add_cancel,zero_add] using hh.add_const (frank a b u)
 let c (i:ℕ)(x y:Slot):= star ((matter (T i)).val x a.x)*(matter (T i)).val y b.x
 have hg(i:ℕ)(x y:Slot):‖c i x y‖≤1:=by
    unfold c; rw [norm_mul,norm_star]; refine (mul_le_mul ((norm_entry _ _ _).trans ?_) ((norm_entry _ _ _).trans ?_) (norm_nonneg _) zero_le_one).trans (by norm_num : (1:ℝ)*1≤1) -- tune
    all_goals exact (CStarRing.norm_of_mem_unitary (matter _).property).le
 let Q(i)(x y:Slot):= V i 1 (skinF a x) (skinF b y)-frank (skinF a x) (skinF b y) u; rw [funext (fun m:ℕ=> show V m (T m) a b-frank a b u=∑ i,∑ j,c m i j * Q m i j from givex ..),show (0:ℂ)=∑ i:Slot,∑ j:Slot,(0:ℂ) by simp]
 refine tendsto_finsetSum _ fun i _=> tendsto_finsetSum _ fun j _=> ?_; apply bendV (f:=fun m=> V m 1 (skinF a i) (skinF b j)-frank _ _ _) ?_ (Eventually.of_forall (fun m=> hg m i j))
 simpa only [sub_self] using (hz (skinF a i) (skinF b j)).sub_const (frank  (skinF a i) (skinF b j) u)
end YM.CF.Emu
