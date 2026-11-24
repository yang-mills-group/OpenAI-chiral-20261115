import YM.CF.Skye.Loam
set_option autoImplicit false
noncomputable section
namespace YM.CF.Skye
open Function Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
variable {n:Side}{u d:ℝ}
abbrev Orbit(n:Side):=Pane n × Ids n
abbrev frameP(X:Ids n)(i:Seat n):=(X i).2.2
def lightly (P:Pane n→Pane n)(u:ℝ)(k:ℕ)(x:Orbit n):Pane n:= fun i=>
 let M:=soup (RG.flags u x.1) k i
 if M.Nonempty then mend P (x.2 (greet M (priorP x.2))).2.1 x.1 i else x.1 i
def sun (P:Pane n→Pane n)(u:ℝ)(k:ℕ)(x:Orbit n):Pane n := gauge (frameP x.2)⁻¹ (lightly P u k (gauge (frameP x.2) x.1,x.2))
lemma sunny_v (P:Pane n→Pane n)(u:ℝ)(k:ℕ)(X:Ids n)(s:Sweep n)(g:Injective (priorP X))(V:Pane n):lightly P u k (flashA s V,bun s X)=flashA s (lightly P u k (V,X)):=by
 funext e; rw [flash]; let M:=soup (RG.flags u V) k (lane s e)
 have ht:soup (RG.flags u (flashA s V)) k e=M.map (boxA s).symm.toEmbedding:=by rw [flagsA,soupS] 
 unfold lightly; dsimp only; rw [ht]; by_cases h:M.Nonempty; swap
 · rw [if_neg (mt map_nonempty.mp h),if_neg h] ; exact flash s V e
 let p:=(X (greet M (priorP X))).2.1; rw [if_pos (map_nonempty.mpr h),if_pos h, show (bun s X _).2.1=s⁻¹*p from ?_,mends,flash]
 change s⁻¹*(X (boxA s _)).2.1=_; unfold M; rw [mast_rev _ s _ _ X h g]
lemma boong(s:Sweep n)(X:Ids n)(x:Pane n): gauge (frameP (bun s X)) (flashA s x)=flashA s (gauge (frameP X) x):= (revG s x (frameP X)).symm
lemma sun_v (P:Pane n→Pane n)(u:ℝ)(k:ℕ)(X:Ids n)(s:Sweep n)(g:Injective (priorP X))(V:Pane n):sun P u k (flashA s V,bun s X)=flashA s (sun P u k (V,X)):=by
 unfold sun; simp only [boong,sunny_v _ _ _ _ _ g]; rw [revG]; congr 2; funext i; unfold frameP; simp only [bun,man,Pi.inv_apply,map_inv] -- tune
lemma gauge_sq (V:Pane n)(X Y:Seat n→E): gauge X (gauge Y V)=gauge (X*Y) V:=by funext i; unfold Lattice.gauge; simp only [Pi.mul_apply]; group
lemma sun_g (P:Pane n→Pane n)(u:ℝ)(k:ℕ)(X:Ids n)(g:Seat n→E)(V:Pane n):sun P u k (gauge g V,threadG g X)=gauge g (sun P u k (V,X)):=by
 have hh:frameP (threadG g X)=frameP X*g⁻¹:= rfl; unfold sun; simp only [hh,_root_.mul_inv_rev, inv_inv,gauge_sq]; simp; congr 1
lemma tied (s:Finset (Seat n))(V W:Pane n)(g h:Seat n→E)(k: Agrees s V W)(u:Set.EqOn g h s): Agrees s (gauge g V) (gauge h W):=fun e y z=> by simp only [Lattice.gauge,k e y z,u y,u z]
variable {P: Pane n→Pane n}{r:ℕ}
lemma lightLegal (h:Basic n P u d r)(x:Orbit n): RG.flags d (lightly P u r x)=∅:= by
 apply broad; intro i; let M:=RG.flags u x.1; let A:= RG.touched i; let B:= lightly P u r x
 obtain ⟨Q,hQ⟩: ∃ Q:Pane n,RG.flags d Q=∅ ∧ Agrees A B Q:=by
    by_cases g:∃ e: reach n,ends e⊆ A ∧ (soup M r e).Nonempty; swap
    · refine ⟨P x.1,h.legal _,fun e k j=>?_⟩; have hp:ends e⊆A:=insert_subset_iff.mpr ⟨k,singleton_subset_iff.mpr j⟩; have hx: ¬ (soup M r e).Nonempty:= fun v=> g ⟨_,hp,v⟩; change (if (soup M r e).Nonempty then _ else _)= _; rw [if_neg hx,h.covers _ _ (not_not.mp (fun g=> hx ((pieV ..).mpr g)))]
    obtain ⟨e,t,p⟩:= g; let s:=(x.2 (greet (soup M r e) (priorP x.2))).2.1; refine ⟨mend P s x.1,(mine h s).legal _, fun a v w=>?_⟩
    have hp:ends a⊆ A:=insert_subset_iff.mpr ⟨v,singleton_subset_iff.mpr w⟩; change (if (soup M r a).Nonempty then _ else _)= _; split; swap; next l=> exact ((mine h s).covers _ _ (not_not.mp (fun g=> l ((pieV ..).mpr g)))).symm
    next u=>
     have hg(y:Seat n)(hy:y∈ A)(x:Seat n)(hx:x∈ A):separation x y ≤ 20:=by have ht:= Work.E01.sep_touched i x hx; have hp:= Work.E01.sep_touched i y hy; have hv:=separation_triangle x i.1 y; rw [separation_comm x i.1] at hv; omega
     change mend P (x.2 (greet (soup M r a) (priorP x.2))).2.1 _ _=_; rw [Finset.Subset.antisymm (dives p (fun i x j y=> hg j (t y) i (hp x))) (dives u (fun i x j y=> hg j (hp y) i (t x)))] -- tune
 by_contra! p; refine absurd (show i.1∈ RG.flags d Q from (RG.flags_spec d Q i.1).mpr ⟨i,by simp [A,RG.touched,square,visits], ?_⟩) ?_; swap

 · simp [hQ.1]
 rw [show faceValue Q i=faceValue B i from Eq.symm (travel_local _ _ _ _ (fun e t x=> hQ.2 e (List.mem_toFinset.mpr t) (List.mem_toFinset.mpr x)))]
 exact p
end YM.CF.Skye
