import YM.CF.Mesa.Row
import YM.CF.Mesa.Knell

/-! Individual Lipschitz SU fill. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Matrix
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {d n:ℕ}
abbrev terrace (d:ℕ):=closedBall (0:Board d) 1
lemma peri_le : Peri (Board d) ⊆ terrace d := sphere_subset_closedBall
lemma smooth_r (u: Ket (Fin n))(hu:u≠0): ContDiffAt ℝ 1 rocket u := ((contDiffAt_norm ℝ hu).inv (norm_ne_zero_iff.mpr hu)).smul contDiffAt_id
lemma beamC (F G:Board d→Keys n){s:Set (Board d)}(h:IsCompact s)(hf:Story s F)(hg:Story s G):Story s fun i=> F i*G i :=
  by
    have ht (v:Keys n×Keys n) : ContDiffAt ℝ 1 (fun v:Keys n×Keys n=>v.1*v.2) v:= ContDiffAt.mul contDiffAt_fst contDiffAt_snd
    have hx : Story s (fun i=>(F i,G i)):=pairer hf hg
    have hu := cruising h hx (g:=fun v:Keys n × Keys n=>v.1 * v.2) (fun x hx=> ht _)
    exact hu
lemma beamH (F:Board d→Keys n){s:Set (Board d)} (h:IsCompact s)(hf:Story s F):Story s fun i=>star (F i):=
  cruising h hf (g:=star) (fun _ _=> (starL' ℝ).toContinuousLinearMap.contDiff.contDiffAt)
lemma bowl (hd:d≤3) (n:ℕ)(F:Board d→Keys (n+1)) (H:Story (Peri (Board d)) F)(h:∀ x∈Peri (Board d),trueS (F x)):
    ∃ G:Board d→Keys (n+1),Story (terrace d) G ∧ EqOn G F (Peri (Board d)) ∧ ∀ x∈terrace d,trueS (G x):=by
  induction n with
  | zero=>
    refine ⟨fun _=>1,⟨_,(LipschitzWith.const _).lipschitzOnWith⟩,fun x hx=> ?_,fun _ _=>suit_one⟩
    have he: (F x).det=1:=(h _ hx).2; ext i j; fin_cases i; fin_cases j; simpa using he.symm
  | succ n ih =>
    let W:= n+1+1
    let f: Board d→Ket (Fin W):= shaft 0 ∘ F
    have ho:=isCompact_sphere (0:Board d) 1
    obtain ⟨K,hK⟩:= cruising ho H (g:=shaft 0) (fun _ _=>shaft_smooth _ _); change LipschitzOnWith K f (Peri (Board d)) at hK
    have hm: MapsTo f (Peri (Board d)) (Peri _):= fun i hi=>by change f i ∈ sphere 0 1; rw [mem_sphere,dist_zero_right]; change ‖f i‖=1; exact shaft_norm (F i) (h _ hi) 0
    obtain ⟨u,hu,hg⟩:= misses (0:Fin (n+2)) 1 (Ne.symm (Fin.succ_ne_zero (0: Fin (n+1)))) hK hd
    change dist u 0=1 at hu; rw [dist_zero_right] at hu
    obtain ⟨Y,hY⟩:= atlas (0:Fin (n+2)) 1 (Ne.symm (Fin.succ_ne_zero (0:Fin (n+1)))) u hu
    let g:= rocket ∘ dome u f
    have ha : ∀ x∈terrace d, trueS (Y (g x))∧ shaft 0 (Y (g x))=g x∧ ContDiffAt ℝ 1 Y (g x):=by
      intro x hx; have hw:= (launched hu hm hg hx).2; exact hY _ (by simpa [g,Peri,mem_sphere] using hw.1) hw.2
    have hi:=isCompact_closedBall (0:Board d) 1
    have hT: Story (terrace d) g:= cruising hi (dome_st hu hK hm) (fun x hx=> smooth_r _ (launched hu hm hg hx).1)
    have hH: Story (terrace d) (Y ∘ g):= cruising hi hT (fun x hx=>(ha _ hx).2.2)
    let R:= Y ∘ g
    have he : EqOn g f (Peri (Board d)):=by
      intro i hx; simp [g,dome,brisk,rocket, show ‖i‖=1 by simpa [Peri,mem_sphere] using hx,show ‖f i‖=1 by simpa [Peri,mem_sphere] using hm hx]
    let Q:= fun i=>star (R i)*F i
    have hk : Story (Peri (Board d)) Q:=by
      obtain ⟨v,hR⟩:= hH; exact beamC _ _ ho (beamH R ho ⟨_,hR.mono peri_le⟩) H
    have hy (i) (t:i∈Peri (Board d)): trueS (Q i)∧ Q i=layer (aside (Q i)):=by
      have hz:=ha i (peri_le t); have hu:= suit_mul (suit_star (show trueS (R i) from hz.1)) (h _ t)
      refine ⟨hu, layer_flat hu ?_⟩
      unfold Q; rw [shaft_back,show shaft 0 (F i)=shaft 0 (R i) from (he t).symm.trans hz.2.1.symm,← shaft_back,show star (R i)*R i=1 from hz.1.1.1]
    obtain ⟨D,hD,p,t⟩:= ih (aside ∘ Q) (cruising ho hk (fun _ _=>aside_cont _)) (fun i hi=> (suit_layer _).mp ((hy i hi).2 ▸ (hy i hi).1))
    refine ⟨fun i => R i * layer (D i),beamC _ _ hi hH (show Story (terrace d) (fun i=>layer (D i)) from cruising (g:=layer) hi hD (fun x hx=>layer_cont _)),fun i h=>?_,fun i h=>suit_mul (ha i h).1 ((suit_layer _).2 (t _ h))⟩
    dsimp only; rw [p h, Function.comp_apply, ← (hy i h).2,show Q i=star (R i)*F i from rfl,← mul_assoc, show R i*star (R i)=1 from (ha i (peri_le h)).1.1.2,one_mul]
end YM.CF.Mesa
