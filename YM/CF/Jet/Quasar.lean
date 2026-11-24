import YM.CF.Jet.Wisps
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Finset MeasureTheory Phase Phase.Sample Lattice Cube Lat
open scoped Topology BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {E X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype X][DecidableEq X]
variable {N m B: Side} {n:ℕ}{A K a:ℝ}{x:E}
abbrev TransK (n:ℕ)(U:E→Bkg N)(x:E)(K:ℝ):=∀ i, Allows n (fun t=> SU.fund (U t i)) x K
lemma factor_is (h:0≤K)(n l:ℕ):∃ M:ℝ, 0≤M∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](N:Side)(U:E→Bkg N) x, TransK n U x K→∀ (i:Site N)(w:Walk), w.length≤l→Allows n (fun t=> SU.fund (travel (U t) i w)) x M:=by
 induction l with
 | zero=> exact ⟨1,zero_le_one,fun E _ _ _ U x L i w g=>by simp [show w=[] by cases w<;>simp_all,travel,SU.fund_one]; exact allows_const x (by simp)⟩
 | succ l ih=>
   obtain ⟨M,g,H⟩:=ih
   let V:= starL' ℝ (A:=Op SU.F) -- check
   let D:= ContinuousLinearMap.mul ℝ (Op SU.F); let T:=max K (‖V.toContinuousLinearMap‖*K); let J:ℝ:= 2^n * ‖D‖*T*M
   refine ⟨max 1 J,lt_of_lt_of_le zero_lt_one (le_max_left ..)|>.le,fun E _ _ N U x L i w q=>?_⟩
   cases w
   · simp only [travel,SU.fund_one]; exact allows_const _ ((show ‖(1:Op SU.F)‖=1 by simp).le.trans (le_max_left ..))
   next k w =>
     have hs:= H E N U x L (i+k.vec) w (by simpa using q)
     have ht:Allows n (fun t=>SU.fund (k.read (U t) i)) x T:=by
        cases k with
        | mk k b=> cases b
                   · exact (L _).mono (le_max_left ..)
                   · exact ((L _).linear V.toContinuousLinearMap le_rfl).mono (le_max_right ..)
     simp only [travel,SU.fund_mul]; exact ((ht.bilinear D hs le_rfl)).mono (le_max_right ..)
lemma act_is (n:ℕ): ContDiff ℝ n (fun v:Op SU.F×Vect=> acts v.1 v.2) :=by
 let T : Op SU.F →L[ℂ] (Vect→L[ℂ]Vect):= (Matrix.toEuclideanCLM (n:=SU.F) (𝕜:=ℂ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
 let R: (Vect→L[ℂ]Vect)→ₗ[ℝ] (Vect→L[ℝ]Vect):=⟨⟨fun F=>F.restrictScalars ℝ,by intros; rfl⟩,fun _ _=>rfl⟩
 let G := R.toContinuousLinearMap.comp (T.restrictScalars ℝ)
 exact (G.contDiff.comp contDiff_fst).clm_apply contDiff_snd
abbrev arr (n:ℕ)(G:E→ArrayF m)(x:E)(K:ℝ):Prop:=∀ i,Allows n (fun t=>(G t i).val) x K
lemma velour (n:ℕ)(h:0≤K)(B:Side)(l:ℕ):∃ C:ℝ,0≤C ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (m:Side) (U:E→Skin m B) x (f:E→ ArrayF m),TransK n U x K→ arr n f x K →∀ (a:Spot m) (w:List (Ramp m)), Moves m a w→w.length≤ l → ∃ L:List (E→ Vect), L.length=w.length∧(∀ u, train m B (U u) (f u) a.1 w= L.map (fun i=>i u)) ∧ (∀ i∈L, Allows n i x C):=by
 induction l with
 | zero=> refine ⟨1,zero_le_one,fun E _ _ _ U x f T Y b w J e=>?_⟩; have he:w=[]:= by simpa using e
          subst w; exact ⟨[],rfl,fun _=>rfl,by simp⟩
 | succ l ih=>
   obtain ⟨C,u,P⟩:= ih; obtain ⟨D,p,R⟩:= factor_is h n (4*B.val)
   let A:=max (max K C) D; have hp: 0≤A:= p.trans (le_max_right ..)
   let X:=fun v:Op SU.F× Vect=> acts v.1 v.2
   obtain ⟨V,w,hV⟩:= compact_allow n hp X (act_is n)
   refine ⟨composeCost n V A,by unfold composeCost; positivity,fun E _ _ m U x f T k b t G L=>?_⟩
   cases t with
   | nil=> exact ⟨[],rfl,fun _=>rfl,by simp⟩
   | cons v t=>
     rcases v with ⟨i,o⟩
     obtain ⟨a,ha,h,hP⟩:= P E m U x f T k i t G.2 (by simpa using L)
     let H(t):= parcel m B (U t) b.1 i.1 o
     let W:List (E→Vect):=(fun y=>(f y i).val) :: a
     use W.map (fun z y=>turn (H y) (z y)); refine ⟨by simp [W,ha],fun y=> ?_,?_⟩
     · rw [train,h]; simp [W,H]
     intro z hz; obtain ⟨z,hb,rfl⟩:= List.mem_map.mp hz
     have hg : Allows n z x A:=by
       rcases List.mem_cons.mp hb with e|e
       · rw [e]; exact (k i).mono ((le_max_left ..).trans (le_max_left ..))
       exact (hP z e).mono ((le_max_right ..).trans (le_max_left ..))
     have he : Allows n (SU.fund ∘ H) x A:=by
       have hQ:separation (address m B i.1) (address m B b.1)≤ B.val:= (separation_comm ..).trans_le (chain_near (b:=b.1) (a:=i.1) (show Prev _ _ _ from G.1).1 _)
       exact (R E (Domain m B) U x T (address m B b.1) (march _ _ o) (march_len _ _ _ hQ)).mono (le_max_right ..)
     have hy:= he.pair hg
     have hQ:=(hV _ hy.value).comp (f:=fun u=> ((SU.fund ∘ H) u,z u)) hy; exact hQ
end YM.CF.Jet
