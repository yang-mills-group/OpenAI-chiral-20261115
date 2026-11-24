import YM.CF.BProof.Stave.Varnish
import YM.CF.BProof.Stave.Core
/-! dimension reduction on Park. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave.Sim
open Function Filter Topology Finset Metric Extension
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal ContDiff
variable {I:Type*}[Fintype I][DecidableEq I]{J:Type*}[Fintype J]{S:Finset I}
abbrev Hub := Fin 3→ℝ
private theorem chart (h:S.Nonempty)(g:S.card≤4): ∃ f:Pool I → Hub, ∃ k:Hub→ Pool I,Tame (Park S) f ∧ Tame (f '' Park S) k ∧ Set.LeftInvOn k f (Park S):=by
 classical
 obtain ⟨j,h⟩:=h; let a:=S.erase j
 have Ha : Nonempty ((a:Type _) ↪ Fin 3):= by apply Function.Embedding.nonempty_of_card_le; simp only [Fintype.card_fin, Fintype.card_coe]; rw [show a=S.erase j from rfl,card_erase_of_mem h]; omega
 let w:= Ha.some
 let f(x:Pool I) : Hub :=∑ i:a, Pi.single (w i) (x i)
 let y(u:Hub): Pool I:= fun i=> if h:i∈a then u (w ⟨i,h⟩) else 0
 let k(u:Hub): Pool I:=update (y u) j (1-∑ i,y u i)
 have hm (x:Pool I)(p:Sim S x): k (f x)=x:= by
    have hz(i:a): f x (w i)=x i:=by unfold f; rw [Finset.sum_apply, sum_eq_single i (fun v _ hv=>Pi.single_eq_of_ne (fun e=> hv (w.injective e.symm)) _) (by simp)]; simp -- Pi zero
    have ht(i:I)(q:i≠ j):y (f x) i=x i:=by unfold y; by_cases ha:i∈ a; rw [dif_pos ha]; exact hz (⟨i,ha⟩:a); rw [dif_neg ha]; exact (p.vanish (fun e=> ha (mem_erase.mpr ⟨q,e⟩))).symm
    ext i; by_cases e:i=j
    · subst i; unfold k; rw [update_self]
      rw [← p.mass,←sum_sub_distrib,sum_eq_single j (fun v _ hv=>by rw [ht v hv,sub_self]) (by simp)]; simp [y,a]
    unfold k; rw [update_of_ne e]; exact ht i e
 refine ⟨f,k,?_,?_,fun x hx=> hm x hx⟩
 · suffices ContDiff ℝ ω f from by
      obtain ⟨u,g,U⟩:=costBall f this 1; exact monk g.le (U.mono (fun x hx=>bound (show Sim S x from hx)) le_rfl)
   apply contDiff_pi.mpr; intro i; simp only [f,Finset.sum_apply]; apply ContDiff.sum; intro l _; by_cases g:i=w l; simp only [g,Pi.single_eq_same]; exact contDiff_apply ℝ _ _; simp only [Pi.single_eq_of_ne (show i≠w l from g)]; exact contDiff_const
 suffices ContDiff ℝ ω k from by
    obtain ⟨u,g,U⟩:= costBall k this (Fintype.card (a:Type _)); apply monk g.le; apply U.mono _ le_rfl
    rintro _ ⟨x,p,rfl⟩; rw [mem_closedBall,dist_zero_right]; unfold f; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun _=>(1:ℝ)) _).trans; · simp
    intro i _; apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro j; by_cases e:j=w i; simp only [e,Pi.single_eq_same, Real.norm_of_nonneg ((show Sim S x from p).pos _)]; exact (show Sim S x from p).bounded _
    rw [Pi.single_eq_of_ne (show j≠w i from e),norm_zero]; exact zero_le_one
 have hu(i):ContDiff ℝ ω (fun x=>y x i):=by by_cases g:i∈a; simp only [y,dif_pos g]; exact contDiff_apply ℝ _ _; simp only [y,dif_neg g]; exact contDiff_const
 apply contDiff_pi.mpr; intro i; by_cases g:i=j
 · subst i; simp only [k,update_self]; exact contDiff_const.sub (ContDiff.sum (fun i _=>hu i))
 simp only [k,update_of_ne (show i≠j from g)]; exact hu _

theorem fee(d:ℝ)(h:0<d):∃ u:ℝ,0<u∧u≤d∧∀ {I:Type*} [Fintype I] [DecidableEq I] (S:Finset I)(F:Pool I→plate J)(A:plate J), S.Nonempty→ S.card≤4→ A∈ King J→Tame (Wall S) F→ (∀ x∈Wall S,Like u A (F x))→ ∃ G:Pool I→plate J,Tame (Park S) G∧ Set.EqOn F G (Wall S)∧∀ x∈Park S,Like d A (G x):=by
 obtain ⟨u,g,c,H⟩:=dough (I:=J) (X:=Hub) d h; refine ⟨u,g,c, fun {I} _ _ S F A p e q w t=>?_⟩
 obtain ⟨f,k,H1,H2,H3⟩:= chart p e; have hv:Set.MapsTo k (f '' Wall S) (Wall S):= fun x ⟨y,hy,hy'⟩ =>hy' ▸ (H3 (wall_le hy)).symm ▸ hy -- test
 have he:f '' Wall S ⊆ f '' Park S:= Set.image_mono wall_le
 obtain ⟨r,R⟩:= (across_iff.image_of_continuousOn H1.li.continuousOn).isBounded.subset_closedBall 0
 obtain ⟨Y,JH,V,U⟩:= H _ _ (max r 1) (F ∘ k) A (by simp [Hub]) he (R.trans (closedBall_subset_closedBall (le_max_left ..))) (one_pos.trans_le (le_max_right ..)) q (fun x hx=>t _ (hv hx)) ((H2.subset he).boundary w hv)
 exact ⟨Y ∘ f,H1.boundary JH (Set.mapsTo_image ..), fun x hx=>by rw [Function.comp_apply,← V (show f x ∈ f '' Wall S from Set.mem_image_of_mem f hx)]; dsimp only [Function.comp_apply]; rw [H3 (wall_le hx)],fun x hx=> U _ (Set.mem_image_of_mem _ hx)⟩ -- tune dsimp
end YM.CF.BProof.Mesh.Stave.Sim
