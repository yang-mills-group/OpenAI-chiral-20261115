import YM.CF.BProof.Gates.Side

/- Produce true flags at price-B-severe, in same gaps. quantitative micro distances constant
 (not increasing with block). When requiring repaired placements, enlarge with static θ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates.Stage.Setup
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing Micro
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}(P:Entice S L a d y){s:Side}(Y:S.Setup L a s d y)
variable (T:PathData G)(θ:ℝ)(x:Pawn Y.yard)
variable {F:Y.yard.FaceS}(U:Config G s)(h:Y.yard.Climate y Y.hall U F)(p:Y.yard.Climbed y Y.hall U F)
include P h
lemma market (i:Y.yard.Index)(t: Y.yard.D i) : Calm (Y.yard.u i) Y.yard.long U (S.scene.charge*mA y):=by
 let q:=S.scene.charge*mA y-4*xi y; rw [show S.scene.charge*mA y=q+4*xi y from (sub_add_cancel ..).symm]; apply calm_D (Y.yard.u i) Y.yard.long y U Y.yard.lL; intro x hx; exact haven Y.yard y Y.hall U F h i t _ ((mem_wash ..).1 hx); intro j; unfold q; linarith only [(P.dull.home j).1] -- tune Calm_D arguments foreach `h`; q? apply not supplied

lemma spend (i:Y.yard.Index)(k: ¬ Y.yard.D i)(a:Bond s)(w:a∈Y.yard.leases i): cd G (formal (Y.yard.u i) Y.yard.long Y.hall U (F i) a) (Angular.hall (Y.yard.u i) Y.yard.long Y.hall U (F i) a) ≤ xi y := by
 let D:=Y.yard; have e:=h.awake _ _ w; rw [slot,if_neg k] at e; let x:= D.baseN i Y.hall U F; have hp : density G (xi y) (x a) (U a)≠0:=by
   rw [density_apply,if_pos e]; apply ne_of_gt; exact ball_positive G (coin_pos ..) P.dull.smallXi -- tune volume ball
 rw [high_price D i y Y.hall U F h.flat k a ((mem_wash ..).2 (leases_w _ i w))] at hp; exact awake y _ _ hp
include p
lemma force (i:Y.yard.Index) : Calm (Y.yard.u i) Y.yard.long U (thresh y/2):=by
 let D:=Y.yard; have hu : ∀ t:ℝ, t ≤ thresh y/2 → Calm (Y.yard.u i) Y.yard.long U t→ Calm (Y.yard.u i) Y.yard.long U (thresh y/2):=fun t p h=> ⟨fun x y j v=> (h.1 x y j v).trans p,fun x y j v=> (h.2 x y j v).trans p⟩
 by_cases k:D.D i; exact hu _ (P.dull.home 0).2 (market P Y U h i k)
 have hx:= P.dull.frame s Y.hall rfl rfl (Y.sized P) P.Fqual (D.u i) U (F i); rw [←length P Y] at hx; obtain ⟨v,e₁,q⟩:=hx (p i k); refine hu _ q (calm_N (D.u i) D.long y Y.hall U (F i) D.lL D.long_pos (fun j u=> spend P Y U h i k j (by rw [leases, if_neg k]; exact u)) v (Face.blend_p ..).le e₁)
lemma sober {l: Angular.Cell s}(t:Y.yard.Marked l): group.chord (faceValue U l) ≤ thresh y/2:=by
 obtain ⟨i,u⟩:= t; rcases whichFace l with ⟨x,p',i',rfl⟩|⟨x,p',i',rfl⟩; exact (force P Y U h p i).1 x p' i' ((wet_t _ _ _ _ _ Y.yard.lL).1 u); exact (force P Y U h p i).2 x p' i' ((wet_p ..).1 u)

lemma markFor (a:Site s)(u: a∈ flags (thresh y) U) {W:Y.yard.Branch}(hx:Y.yard.Evap S.κ y U W):
    ∃ i:Y.yard.Index,Y.yard.Gap i (time a) ∧ ∃ p:Space s,(i,p)∈Y.yard.severe S.κ y U ∧ Grid.dist p (BProof.space a)≤4:=by
 obtain ⟨z,b,e⟩:= (flags_spec ..).1 u; have hv:¬Y.yard.Marked z:=fun h' => not_lt_of_ge ((sober P Y U h p h').trans (by linarith [show 0<thresh y from coin_pos ..])) e
 let D:=Y.yard
 obtain ⟨i,hi⟩: ∃ i:Y.yard.Index,touched z ⊆ Y.yard.gap i:=by
    rcases whichFace z with ⟨x,p,j,rfl⟩|⟨x,p,j,rfl⟩; rw [marked_n] at hv; obtain ⟨a,v⟩:=not_not.mp hv; exact ⟨a,(wet_t _ _ _ (D.v a) _ D.dD).2 v⟩
    obtain ⟨a,h⟩:= unmark_center Y.yard (hf x p j) hv; exact ⟨a,(wet_p ..).2 h⟩
 let K(t:Site s):= (i,BProof.space t); have H(x: Site s)(p:x∈touched z): Y.yard.Gap i (time x):=mem_strip.mp (hi p)
 refine ⟨i,H _ b,?_⟩; by_contra! u
 have hp' (q:Site s)(p:q∈touched z):K q∉ D.severe S.κ y U:=by
    have hu : Grid.dist (BProof.space q) (BProof.space a) ≤4:=by
       apply Grid.dist_le.mpr; intro i; have hg:= ((Grid.triangle q z.1 a).trans (Nat.add_le_add ((Grid.dist_symm q z.1).trans_le (Work.E01.sep_touched _ _ p)) (Work.E01.sep_touched _ _ b))); exact Grid.dist_le.mp (show Grid.dist q a≤4 from hg) i.succ
    exact fun h=>hu.not_gt (u (BProof.space q) h)
 apply e.not_ge; rw [←show lRead 1 U=U from pull_id ..]; apply chord_price S.K (Y.yard.roll W) y 1 U P.dull.ink; intro t; rw [show sendEdge 1 0 (positions z t) = positions z t from ?_]; swap
 · unfold sendEdge; simp [Step.used, Step.rotate, posDir, affine]; -- tune
 have he:= (curl_positions z t).1; generalize positions z t=v at *; rcases whichBond v with ⟨x,p,rfl⟩|⟨x,p,j,rfl⟩
 · have hk: 4*(0:ℕ)+4≤Y.yard.long:=by have :=P.wide; rw [length P Y]; omega
   exact tone_vert Y.yard W h hx i x p hk (Y.yard.outside_gap i _ x (H _ he))
 exact tone_gap Y.yard W h hx i x p (H _ he) j (by have hv:=hp' _ he; change K (BProof.join x p)∉_ at hv; simpa only [K,space_join] using hv)
end YM.CF.BProof.Gates.Stage.Setup
