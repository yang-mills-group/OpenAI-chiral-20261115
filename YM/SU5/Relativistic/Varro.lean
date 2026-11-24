import YM.SU5.Relativistic.Finer
import YM.SU5.FiniteGaugeData.Marked.Variation.Linoleum
/-! # permit while STILL epsilon-after-density. Rune exact. revenue before theta. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Papyrus.Franc.Loaves
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip Flare BPress.Spin.Blank
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu
open Lifted Pea Omelet Pannier Pannier.Chancel Afterglow.Satin
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra
variable {S: Finset Cover} {L:List Wine}{ε:ℝ}{K:ℕ}{d:ℝ}(u:0≤d)(f:∀ ε>(0:ℝ),∃ γ>(0:ℝ),∃ w:ℕ,∀ n:Side,K ≤ n.val→ Winter 4 d n γ w ε)
include u f
private lemma cay(k:ℕ)(a:ℝ)(t:0<a)(A:Bool→Bool→ Staff) : ∃ γ>(0:ℝ),∃ w:ℕ,∀ b c:Bool, (A b c).Stage 4 K d w γ a:=by
 let F(b c:Bool):=A b c; choose c p s h using fun b c=> Staff.playsA 4 d u f (A b c) a t
 let W:= s true true+s true false+s false true+s false false
 let G:=min (min (c true true) (c true false)) (min (c false true) (c false false))
 refine ⟨G,lt_min (lt_min (p _ _) (p _ _)) (lt_min (p _ _) (p _ _)),W,fun b v=>?_⟩
 apply Staff.stage_big 4 d _ (h b v) (show W≥s b v from (by unfold W; cases b <;> cases v <;> omega)); swap; · rfl
 unfold G; cases b <;> cases v <;> grind -- tune
private def idol (m:ℕ)(p q:Bool):Staff:= ((if p then Staff.pay else (.add .one (.neg .pay)) : Staff).mul (Loaves.colors m q))
omit u f
private lemma idolH {n:Side}(P:Op (Single n))(i:Bite)(k:ℕ)(b:Bool) : acts ((idol k b i.hand).stem (tickA n) P) (i.loc n) = acts (ease b P) (Straw P k i):=by
 unfold idol ease Straw; rw [Staff.stem,act_mul]; cases b; simp only [Bool.false_eq_true,↓reduceIte]; change acts (1 + -P) _= acts (1-P) _; rw [sub_eq_add_neg]; rfl
 rfl
include u f
open Staff
private lemma fork (D:ℝ)(v:∀ (N:Side)(M:Tulip.Male), IsStarProjection (spar 4 M (1: Pane N)) →∀ j:ℕ,∀ i:Bite, ‖Straw (spar 4 M (1: Pane N)) j i‖ ≤ D)(ε:ℝ)(h:0<ε) (T:Finset Cover): ∃ W:Finset Cover, T ⊆ W ∧ ∀ᶠ k:ℕ in atTop, ∃ γ> (0:ℝ),∃ w:ℕ,∀ n:Side, K≤ n.val→∀ M:Tulip.Male,IsStarProjection (spar 4 M (1: Pane n))→∀ P:Pane n,Guard P d → Rightful (Lattice.halo w (terrace n T)) P 1 γ→IsStarProjection (spar 4 M P)→∀ i:Bite,nodeC i.root ∈ T →let X:=Straw (spar 4 M P) k i; ‖X‖≤ 1+D ∧∀ b:Bool, comfy (modesIn n (terrace n W)) b (spar 4 M P) X ε:=by
 let a:= min 1 (ε/3); have e:0<a:=lt_min (by norm_num) (by positivity); obtain ⟨q,H⟩:=(stilt_p e).exists; obtain ⟨γ',u',w,x⟩:=cay u f q a e (idol q)
 let W:=liner T w; refine ⟨W,liner_here ..,?_⟩; filter_upwards [eventually_ge_atTop q] with k t
 let Y:= idol k; obtain ⟨γ,g,z,hp⟩:=cay u f k a e Y; obtain ⟨τ,hτ,l,t0⟩:=cay u f k a e (fun u _=> Loaves.colors k u)
 let ε':=min γ τ; let L:=max z l; refine ⟨ε',lt_min g hτ,L,fun n v' M p₀ P g₀ h' v₀ i i₀=>?_⟩
 intro X
 let C:=terrace n T; let Q:=spar 4 M P; let P':=spar 4 M (1: Pane n); let B:=tickA n
 let V:=Vo C; let I:=i.loc n; let Mc:=(Loaves.colors k i.hand); let Do:= (Straw P' k i); let BQ:= (Straw P' q i)
 have he:acts V I=I:= i.pace _ i₀; have hx:‖I‖=1:=i.normP n
 have hu(Z C':Op (Single n))(h:‖(Z-C')*V‖≤a): ‖acts Z I-acts C' I‖≤ a:=by rw [←act_sub]; nth_rw 1 [←he]; rw [←act_mul]; exact (Flare.opy ..).trans (by rwa [hx,mul_one])
 constructor
 · refine (norm_le_norm_sub_add X Do).trans (add_le_add ?_ (v n M p₀ k i)); have hv:‖(Mc.stem B Q-Mc.stem B P')*V‖≤a:=(stage_big _ d _ (t0 i.hand i.hand) (le_max_right z l) (min_le_right γ τ) le_rfl v' M C p₀).2 P g₀ h' v₀; exact (hu _ _ hv).trans (min_le_left ..)
 intro b; let F:=Vo (terrace n W); let Z:=1-F
 have ht(Y U:Ket (Single n)) : ‖acts Z Y‖ ≤ ‖Y-U‖+‖acts Z U‖:=by rw [←sub_add_cancel (acts Z Y) (acts Z U),←map_sub]; exact (norm_add_le ..).trans (add_le_add_left ((opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).one_sub.norm_le Z))) _)
 let J0:= ease b P'; let U0:= acts (ease b Q) X; let v1:= acts J0 Do; let v2:= acts J0 BQ
 have hz:‖U0-v1‖≤a:=by have hp:‖((Y b i.hand).stem B Q-(Y b i.hand).stem B P')*V‖≤a:=(stage_big _ d _ (hp b i.hand) (le_max_left z l) (min_le_left ..) le_rfl v' M C p₀).2 P g₀ h' v₀; rw [show U0=_ from (idolH Q i k b).symm, show v1= _ from (idolH P' i k b).symm]; exact hu _ _ hp
 have hs:‖v1-v2‖≤a:=by unfold v1 v2; rw [←map_sub]; exact (opy ..).trans ((mul_le_of_le_one_left (norm_nonneg _) ((show IsStarProjection J0 from by cases b; exact p₀.one_sub; exact p₀).norm_le J0)).trans (H _ _ p₀ _ t i))
 have hv: ‖acts Z v2‖ ≤ a:=by
    let X0:=Lattice.halo w C
    have he:Z=Vo (terrace n W)ᶜ:=Eq.symm (Vo_neg ..); let K':=(idol q b i.hand).stem B P'
    have hw: ‖Z*(K'*V)‖≤a:=by rw [he]; apply (Staff.cut_snap (compl_subset_compl.mpr (show X0⊆terrace n W from linen_contains ..)) _).trans; exact (x b i.hand v' M C p₀).1
    rw [show v2=acts K' I from (idolH P' i q b).symm]; nth_rw 1 [← show acts V I=I from (i.pace _ i₀)]; rw [←act_mul _ V, ←act_mul]; exact (opy ..).trans (by rwa [hx,mul_one])
 apply (ht U0 v1).trans; exact (add_le_add hz ((ht v1 v2).trans (add_le_add hs hv))).trans (by linarith [show a≤ε/3 from min_le_right ..])
variable (T:S.Nonempty)
include T
lemma audience (ε:ℝ)(t:0<ε)(H:AreaW false S L) : ∃ ζ> (0:ℝ),∀ z:ℂ,0<‖z‖→‖z‖≤ζ→∃ W:Finset Cover, S⊆W∧∃ η>(0:ℝ),4*η≤ε*‖z‖ ∧∀ᶠ m in atTop,∃ γ>(0:ℝ),∃ w l:ℕ,∀ n:Side,K≤ n.val→l ≤ n.val→Even n.val→∀ M:Tulip.Male,l≤M.val.val→ IsStarProjection (spar 4 M (1:Pane n))→∀ U: Pane n,∀ X:Fields n,Guard U d → Rightful (Lattice.halo w (terrace n W)) U 1 γ → Rightful (terrace n S) X.1 1 γ→∀ Q:IsStarProjection (spar 4 M U), Nought (Saber (B:=tickA n) Q m) (whisper z (tallyW L) (motet n L X)) (spar 4 M U) η (ε*‖z‖) (modesIn n (terrace n W)) :=by
 obtain ⟨C',e,P⟩:=stilt_h; let C:=1+C'; have hc:1≤C:=le_add_of_nonneg_right e.le
 obtain ⟨ζ,hp,X⟩:= counsel L H C hc ε t
 refine ⟨_,hp,fun z v q=>?_⟩; obtain ⟨η,r,p,A⟩:=X _ v q; obtain ⟨δ,g,Y⟩:=honors (billP L) C (zero_lt_one.trans_le hc) η r; obtain ⟨W,x,X'⟩:=fork u f C' P δ g S
 refine ⟨W,x,η,r,p,?_⟩; filter_upwards [remiss u f T r H, X'] with m v p
 obtain ⟨γ,o,s,l,h⟩:=v; obtain ⟨γ',o',b,i⟩:=p; refine ⟨_,lt_min o o',max s b,l,fun n a g el M e P Z F hx hv hf q=>?_⟩
 let Q:=spar 4 M Z; let X:=terrace n W; have hp:terrace n S⊆ X:= image_subset_image x
 have ht:= h n a g el M e P Z F.1 hx (Staff.rightfulInv hv (crease (le_max_left ..) hp) (min_le_left ..)) (Staff.rightfulInv hf (subset_refl _) (min_le_left ..)) q
 let R':= F.1
 have hu(j:Bite)(w:j∈billP L):‖Straw Q m j‖≤ C ∧∀ y:Bool, comfy (modesIn n X) y Q (Straw Q m j) δ:= i n a M P Z hx (Staff.rightfulInv hv (crease (le_max_right ..) hp) (min_le_right ..)) q j (by obtain ⟨i,p,x⟩:=List.mem_flatMap.mp w; exact (H i p).sewn _ x)
 obtain ⟨T',v,y,r⟩:=Y q (Straw Q m) (fun i p=>(hu i p).1) (fun i p=>(hu i p).2)
 apply A F Q q _ _ T' v y (fun i h=>⟨(hu i h).1,r i h⟩); obtain ⟨x,k⟩:=phoz q; exact ⟨x,k,ht x k⟩
end YM.CF.Papyrus.Franc.Loaves
#print axioms YM.CF.Papyrus.Franc.Loaves.audience
