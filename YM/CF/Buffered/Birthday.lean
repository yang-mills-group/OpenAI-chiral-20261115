import YM.CF.Buffered.Duet
import YM.CF.Emu.Fame
/-! preparatory coupon payments, fixed R and arbitrary holonomy. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial Gall
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{F K T D U:Op (Single N)} {d:Candle}{r v e C:ℝ}
namespace Lead
variable (A:Lead R)
private lemma size_sing (f:Bool)(R:ℕ):‖Lead.sing R f‖=R^3/5:=by cases f <;> simp [Lead.sing,phaseF]
private lemma earned (V:Pane N)(i j:Slot): ‖A.coil V i j‖≤1:= (norm_entry (matter _).val _ _).trans_eq (CStarRing.norm_of_mem_unitary (matter _).property)
abbrev maximumV(R:ℕ)(x:ℝ):= 5*(R:ℝ)^3*(x+1)^2
lemma maximumV_nn(R:ℕ)(x:ℝ):0≤ maximumV R x:=by unfold maximumV; positivity
private lemma size_five : five.card=5:=(colors_card _).trans rfl
private abbrev lift_b (x:Cover)(p:Op (Single N))(g:Bool)(i:SpinIdx)(u:Slot):= iceT p (g,basisC N x i u)
private lemma scl (x:Cover)(g:Bool)(i:SpinIdx)(u:Slot): ∃ s:ℂ,‖s‖=1∧ ∀ L:Op (Single N),lift_b x L g i u=s • iceT L (Gall.artW (g,Lifted.index N x i u)):=by
 let s:= Lifted.winding N x; have h:‖s‖=1:=Rush.fee_norm _
 refine ⟨s,h,fun p=>?_⟩; unfold lift_b basisC Gall.artW iceT; rw [map_smul]; rcases g with _|_
 · exact map_smul ..
 change star (create (s • _))=s • star _; rw [map_smul,star_smul,show star s=s from fee_real _]
private lemma lift_n (x:Cover)(g:Bool)(i:SpinIdx)(u:Slot) (h:Billow e F) : ‖lift_b x F g i u‖ ≤ e+1:=by
 obtain ⟨s,p,v⟩:=scl (N:=N) x g i u; rw [v,norm_smul,p,one_mul]; exact Gall.bill_p h _
private lemma ice_cost {n:Type*} [LinearOrder n] [Fintype n] {X Y:Op n} (h:Billow e (X-Y)) (g:Bool)(i:n): ‖iceT X (g,basisKet i)-iceT Y (g,basisKet i)‖ ≤ e:=by
 cases g; swap
 · let v:=basisKet i; have he: Fock.remove (acts (1+star X) v)-Fock.remove (acts (1+star Y) v)=Fock.remove (acts (star (X-Y)) v):=by unfold Fock.remove; rw [act_add,act_add,map_add,map_add,star_add,star_add,star_sub,act_sub,map_sub,star_sub]; abel -- name? simplify again
   change ‖Fock.remove (acts (1+star X) v)-Fock.remove (acts (1+star Y) v)‖≤_; exact he ▸ ((Flare.cost_pe true (acts (star (X-Y)) v)).trans (h i).2)
 let v:=basisKet i; change ‖create (acts (1-X) v)-create (acts (1-Y) v)‖≤_
 rw [show create (acts (1-X) v)-create (acts (1-Y) v)= -create (acts (X-Y) v) from (by rw [act_sub,act_sub,act_sub,map_sub,map_sub,map_sub]; abel), norm_neg]; exact (Flare.cost_pe false _).trans (h i).1
private lemma lift_l (x:Cover)(g:Bool)(i:SpinIdx)(u:Slot) (h:Billow e (F-K)) : ‖lift_b x F g i u-lift_b x K g i u‖ ≤ e:=by
 obtain ⟨s,p,v⟩:=scl (N:=N) x g i u; rw [v,v,←smul_sub,norm_smul,p,one_mul]; exact ice_cost h g _
lemma lasting_n (V:Pane N)(h:Billow e F)(p:0≤e): ‖A.lasting V F‖ ≤ maximumV R e:=by
 unfold lasting; rw [norm_smul, size_sing]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (g:=fun _=> (e+1)^2) (fun j _=>?_))))) (by positivity)); swap
 · rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (earned ..)).trans ((norm_mul_le ..).trans ((mul_le_mul (lift_n _ true _ j h) (lift_n _ false _ i h) (norm_nonneg _) (by positivity)).trans_eq (sq _).symm))
 simp only [sum_const,size_five,nsmul_eq_mul,Nat.cast_ofNat]; apply le_of_eq; unfold maximumV; ring
private lemma operate {n:Type*}[Fintype n][DecidableEq n] (i j k l:Op n)(h:‖i-k‖ ≤ v)(w:‖j-l‖≤v)(g:‖k‖≤C)(e:‖j‖≤C): ‖i*j-k*l‖≤2*v*C:=by rw [show i*j-k*l=(i-k)*j+k*(j-l) from (by rw [sub_mul,mul_sub]; abel)]; apply (norm_add_le ..).trans; exact (add_le_add ((norm_mul_le ..).trans (mul_le_mul h e (norm_nonneg _) ((norm_nonneg _).trans h))) ((norm_mul_le ..).trans (mul_le_mul g w (norm_nonneg _) ((norm_nonneg _).trans g)))).trans_eq (by ring) -- tune
abbrev waveMix(R:ℕ)(v:ℝ):= 10*(R:ℝ)^3*(v+1)
lemma lasting_m (V:Pane N)(h:Billow v (F-K))(g:Billow e F)(t:Billow e K): ‖A.lasting V F-A.lasting V K‖ ≤ waveMix R e * v:=by
 unfold lasting; rw [←smul_sub,norm_smul,size_sing]; simp_rw [←sum_sub_distrib,←smul_sub]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (g:=fun _=>2*v*(e+1)) (fun j _=>?_))))) (by positivity)); swap
 · rw [norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) (earned ..)).trans (operate _ _ _ _ (lift_l _ true _ j h) (lift_l _ false _ i h) (lift_n _ true _ j t) (lift_n _ false _ i g))
 simp only [sum_const,size_five,nsmul_eq_mul,Nat.cast_ofNat]; apply le_of_eq; unfold waveMix; ring
noncomputable def brass := Classical.choose Pic.gulf
lemma brass_p : 0<brass := zero_lt_one.trans_le (Classical.choose_spec Pic.gulf).1
lemma lasting_t (Y Z:Pane N)(h:lawnK Y Z v)(t:Billow e F)(p:0 ≤ e)(b:0≤v) : ‖A.lasting Y F-A.lasting Z F‖≤2*brass*R*maximumV R e * v:= by
 unfold lasting; rw [←smul_sub,norm_smul,size_sing]; simp_rw [←sum_sub_distrib, ←sub_smul]
 apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (fun i _=> (norm_sum_le ..).trans (sum_le_sum (g:=fun _=> (brass*((2*R)*v))*(e+1)^2) (fun j _=> ?_))))) (by positivity)); swap
 · rw [norm_smul]; have hg:=brass_p; refine mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity)
   · apply (show ‖A.coil Y _ _-A.coil Z _ _‖≤Cube.cmp matter (A.laps Y) (A.laps Z) from norm_entry ((matter _).val-(matter _).val) _ _).trans; refine ((Classical.choose_spec Pic.gulf).2 _ _).trans ?_; rw [laps_t,laps_t]; refine mul_le_mul_of_nonneg_left ((Emu.frost_k h A.traceV _).trans_eq ?_) hg.le; rw [A.costs]; push_cast; rfl
   exact (norm_mul_le ..).trans ((mul_le_mul (lift_n _ true _ j t) (lift_n _ false _ i t) (norm_nonneg _) (by positivity)).trans_eq (sq _).symm)
 simp only [sum_const,size_five,nsmul_eq_mul,Nat.cast_ofNat]; apply le_of_eq; unfold maximumV; ring
end Lead
namespace Melody
variable (A:Melody B R)
abbrev maximum (R:ℕ)(e:ℝ):= Lead.maximumV R e
abbrev extra (R:ℕ)(e:ℝ):= maximum R e+maximum R e^2
abbrev cuts (R:ℕ)(e:ℝ):= extra R e+‖compared‖+‖P20‖
abbrev Hlead(R:ℕ)(e:ℝ):= ((1+2*maximum R e)*Lead.waveMix R e)
abbrev Hbody(R:ℕ)(e:ℝ):= (1+2*maximum R e)*(2*Lead.brass*R*maximum R e)
lemma note_n (Y : Pane N)(b:Bool)(p:Billow e F)(t:0≤e): ‖noteL A Y b F‖ ≤ cuts R e:=by
 have ht:0 ≤ maximum R e:=Lead.maximumV_nn ..; unfold noteL cuts compare; cases b; all_goals simp only [Bool.false_eq_true,ite_false,ite_true]; apply (norm_sub_le ..).trans; rw [norm_smul, norm_one,mul_one]; unfold extra
 · exact le_trans (add_le_add_left (A.first.lasting_n _ p t) _) (by unfold maximum at *; nlinarith [norm_nonneg compared]) -- add? 
 rw [Complex.norm_real]; apply le_trans (add_le_add_left (le_trans (norm_mul_le ..) ((mul_le_mul (A.first.lasting_n _ p t) (A.last.lasting_n _ p t) (norm_nonneg _) ht).trans_eq (sq _).symm)) _); unfold maximum at *; nlinarith [norm_nonneg P20]
lemma note_l (Y:Pane N)(b:Bool)(h:Billow v (F-K))(p:Billow e F)(t:Billow e K)(a:0≤v)(w:0≤e): ‖noteL A Y b F-noteL A Y b K‖≤ Hlead R e * v:=by
 let L:=Lead.waveMix R e; have hp:0≤L:=by unfold L Lead.waveMix; positivity
 have hv:0≤ maximum R e:=Lead.maximumV_nn ..
 unfold noteL; cases b; all_goals simp only [Bool.false_eq_true,ite_false,ite_true,sub_sub_sub_cancel_right]
 · exact le_trans (A.first.lasting_m Y h p t) (by unfold Hlead; nlinarith only [mul_nonneg (show 0≤L*v from by positivity) hv])
 exact (Lead.operate _ _ _ _ (A.first.lasting_m Y h p t) (A.last.lasting_m Y h p t) (A.first.lasting_n _ t w) (A.last.lasting_n _ p w)).trans (by unfold Hlead maximum; have he:0≤ Lead.waveMix R e * v:=mul_nonneg hp a; linarith)
lemma note_tie (Y Z:Pane N)(f:Bool)(v':0≤v)(h:lawnK Y Z v)(p:Billow e F)(t:0≤e): ‖noteL A Y f F-noteL A Z f F‖≤ Hbody R e * v:=by
 let L:=2*Lead.brass*R*maximum R e; have hv:0≤ maximum R e:=Lead.maximumV_nn ..; have hp:0≤L:=by unfold L; have he:=Lead.brass_p; positivity
 have he:0 ≤ (2*Lead.brass*R*maximum R e)*v:=mul_nonneg hp v'
 unfold noteL; cases f; all_goals simp only [Bool.false_eq_true,ite_false,ite_true,sub_sub_sub_cancel_right]
 · exact le_trans (A.first.lasting_t Y Z h p t v') (by unfold Hbody; nlinarith only [mul_nonneg he hv])
 exact (Lead.operate _ _ _ _ (A.first.lasting_t Y Z h p t v') (A.last.lasting_t Y Z h p t v') (A.first.lasting_n _ p t) (A.last.lasting_n _ p t)).trans (by unfold Hbody maximum; unfold maximum at he; linarith)
#print axioms note_tie
end Melody
end YM.CF.Buffered.Ballad
