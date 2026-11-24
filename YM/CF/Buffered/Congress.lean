import YM.CF.Buffered.Birthday
/-! Every label is a lead. Can depend arbitrarily on what the other sites are;
localized Eins about each in NATIVE period (pay x,k after R and orientation
spin tasks). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial Gall
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R w:ℕ}{B N : Side}{I : Type*}{C e v a b:ℝ}

def Fresh (v:ℕ) (S:Single N→I) (i:I) (x:Cover) := ∀ j:Single N,separation (node j.1.1) (wrap (More N) (nodeC x)) ≤ v → S j=i
def Payments (v:ℕ) (S:Single N→I)(P:I→Melody B R) := ∀ i:I, Fresh v S i (P i).first.birth∧ Fresh v S i (P i).first.death ∧ Fresh v S i (P i).last.birth ∧ Fresh v S i (P i).last.death
variable [DecidableEq I] {S:Single N→I} {i:I}
private lemma prior {d:Cover} (h:Fresh w S i (x:= d)) (F:Op (Single N))(q:Ranged w F)(b:Bool)(j:SpinIdx)(a:Slot) : Sector (variety S i) true (iceT F (b,basisC N d j a)):=by
 let T:Op (Single N):= if b then star F else F
 have ht:Ranged w T:=by unfold T; split; exact q.star; exact q
 let R:Op (Single N):= if b then 1+star F else 1-F
 have hp:Ranged w R:=by
    intro i v he; have hw:T i v=0:=ht i v he; have hv:i≠v:=fun h=>by subst i; rw [separation_self] at he; omega
    cases b <;> simp_all only [R,T,ite_true,ite_false,Bool.false_eq_true,Matrix.add_apply,Matrix.sub_apply,Matrix.one_apply,sub_zero, add_zero]
 let u:= acts R (basisC N d j a)
 have he:withinM (variety S i) u:=by
   apply (within_test ..).2; intro v p; unfold u basisC; simp only [map_smul,WithLp.ofLp_smul, Pi.smul_apply, basis_act]; apply smul_eq_zero_of_right; apply hp; apply lt_of_not_ge; intro he; apply p; exact mem_filter.mpr ⟨mem_univ _, h v (by rw [←node_of]; exact he)⟩
 change Sector _ _ (creed b u); cases b; exact Sector.makeP u he; exact (Sector.makeP u he).contr
lemma Lead.familyF {A:Lead R}(h:Fresh w S i A.birth)(t:Fresh w S i A.death)(P:Op (Single N))(p:Ranged w P)(Y: Pane N): Sector (variety S i) false (A.lasting Y P):= by apply Sector.scale; apply Sector.sumS; intro i _; apply Sector.sumS; intro j _; apply Sector.scale; exact (prior t P p true (dnSpin _) j).mul (prior h P p false (upSpin _) i)
omit [DecidableEq I] in
private lemma lobby_pos (i:ℝ)(R:ℕ):0 ≤ Melody.cuts R i := by unfold Melody.cuts Melody.extra; have he:0 ≤ Melody.maximum R i:=Lead.maximumV_nn ..; positivity
variable [Fintype I]
lemma Lead.billC (S:Single N→I)(V:Pane N)(F:Op (Single N))(A:Lead R) : ChangeBill S 2 (A.lasting V F):= by unfold Lead.lasting; refine ChangeBill.scale (ChangeBill.series _ _ fun i _=> ChangeBill.series _ _ fun j _=> ChangeBill.scale ?_ _) _; exact (change_ice S _ _).mul (change_ice S _ _)
lemma Melody.billC (S:Single N→I)(V:Pane N)(F:Op (Single N))(A:Melody B R)(b:Bool) : ChangeBill S 4 (A.noteL V b F):=by
 unfold noteL; apply ChangeBill.sub _ ((change_one S 4).scale _); split; exact (A.first.billC S V F).mul (A.last.billC S V F); exact (A.first.billC S V F).le (by omega)
omit [Fintype I] in
lemma Melody.secs {P:I→Melody B R} (V:Pane N)(F:Op (Single N))(h:Payments w S P)(u:Ranged w F)(b:Bool) : Sector (variety S i) false ((P i).noteL V b F):=by
 obtain ⟨e,t,a,b'⟩:= h i
 unfold noteL; rw [sub_eq_add_neg]; have v :Sector (variety S i) false (-(compare b • (1:FC _))):=by rw [←neg_smul]; exact Sector.one.scale _
 split; exact (((P i).first.familyF e t F u V).mul ((P i).last.familyF a b' F u V)).add v; exact (((P i).first.familyF e t F u V)).add v
private lemma later (c:ℝ) (p:0<c)(t: 1≤v)(e:ℝ)(r: 0 < e): ∃ g u:ℝ,0<g∧g≤1∧0<u∧ (g+u)*c ≤ e/2 ∧ g*c ≤ e/v^4:=by
 let g:=min 1 (min (e/v^4/c) (e/(4*c))); have hx:0<v:=zero_lt_one.trans_le t; have hg:0<g:=lt_min (by norm_num) (lt_min (by positivity) (by positivity)); have ht:= le_min_iff.mp ((min_le_right 1 _):g≤ min (e/v^4/c) (e/(4*c))); refine ⟨g,g,hg,min_le_left ..,hg,by nlinarith [(le_div_iff₀ (by positivity : 0<4*c)).1 ht.2],(le_div_iff₀ p).1 ht.1⟩

-- local subsidy paid, amortized across error cost
namespace Melody
lemma toured (R j:ℕ)(p:1≤j) (r:ℝ)(hr:0<r)(C:ℝ)(hc:0<C)(e:ℝ)(hy:0<e) : ∃ a y:ℝ,1≤a∧0<y∧ ∃ v t:ℕ, ∀ (N:Side),v ≤ N.val → Pad j N → ∀ (I:Type*)[Fintype I][DecidableEq I] (S:Single N→I) (P:I→Melody B R) (b:Bool), (∀ i,LedgerR N j r C (e/2) b (P i)) → Payments t S P → ∀ (U:Fields N) (d:Candle)(F:Slide N d), lawnK U.1 (Kea.tax d) y → ∀ (M:Jill.Male) (L D K:Op (Single N)),Clad (Dofu N (field F j M)) (tickA N) L D K →∀ V:Stag N→Peb, Dofu N V=laneP (tickA N) L K →(∀ i:Slot,FormU (F.u i) j M r C (trackF F V i))→∃ A Z:I→ FC (Single N),(∀ i, Dress (Dofu N V) ((P i).goal b U) (A i+Z i)) ∧ (∀ i,Sector (variety S i) false (A i))∧ (∀ i,ChangeBill S 4 (Z i))∧ Pot (Tset N) A Z e a 4 := by
 obtain ⟨G,h,A⟩:= Gall.fame p hr hc
 let c:=cuts R (G+1); let a:=max 1 (c/e); obtain ⟨y,z,hy',t,hz,l,l'⟩:= later (Hlead R (G+1)+Hbody R (G+1)+1) (show 0<_ from by
    have he:0 ≤ maximum R (G+1):=Lead.maximumV_nn ..; have hv:=Lead.brass_p; unfold Hlead Hbody Lead.waveMix; positivity) (le_max_left 1 (c/e)) e hy
 obtain ⟨w,k,U⟩:=Glaze.range_bill p hr hc y hy'
 refine ⟨a,z,le_max_left ..,hz,k,w,?_⟩; intro N v u I _ _ S P b T e' V d F f M L D K W' Q W H'
 let D':=Dofu N Q
 have hD:Billow G D':=A _ _ u.1 H'
 obtain ⟨Z,Y,Z'⟩:= U u v F M Q H'
 let m(i:I):=(P i).noteL V.1 b D'; let g(i:I):=(P i).noteL V.1 b Z
 have hv:Billow (G+1) D':=fun i=>⟨(hD i).1.trans (by linarith),(hD i).2.trans (by linarith)⟩
 have hk:Billow (G+1) Z := by
    have he: Billow y (Z-D'):=fun i=> by rw [← neg_sub (a:=D') (b:=Z),act_neg,star_neg,act_neg,norm_neg,norm_neg]; exact Z' i -- param names
    have hh: Billow (G+y) Z :=by convert hD.add he using 1; abel
    exact fun i=>⟨(hh i).1.trans (by linarith),(hh i).2.trans (by linarith)⟩
 have he:0 ≤ maximum R (G+1):=Lead.maximumV_nn ..; have hβ:=Lead.brass_p
 have hε:0 ≤ Hlead R (G+1):=by unfold Hlead Lead.waveMix; positivity
 have hζ:0 ≤ Hbody R (G+1):=by unfold Hbody; positivity
 let u':=Hlead R (G+1)+Hbody R (G+1)+1; have hl:Hlead R (G+1) ≤ u':=by unfold u'; linarith
 have hx:Hbody R (G+1) ≤ u':=by unfold u'; linarith
 have hY(i:I):‖m i-g i‖≤y*u':= (note_l _ V.1 b Z' hv hk hy'.le (by linarith)).trans ((mul_le_mul_of_nonneg_right hl hy'.le).trans_eq (mul_comm ..))
 refine ⟨g,m-g,fun i=>by rw [Pi.sub_apply,add_sub_cancel]; unfold m D'; rw [W]; exact (P i).dressed V W' b,fun i=> Melody.secs _ _ e' Y b,fun i=>ChangeBill.sub ((P i).billC S _ _ b) ((P i).billC S _ _ b),?_,?_,fun i=> (hY i).trans l'⟩
 · intro i; let x:= Tset N
   let C:= (P i).noteL (Kea.tax d) b D'
   have hg:‖C x x‖≤ e/2:= T i F Q M H' _ _ _ W' W
   have hw: ‖m i x x-C x x‖ ≤ z*u':= (norm_entry (m i-C) x x).trans ((show ‖m i-C‖ ≤ Hbody R (G+1)*z from (P i).note_tie _ _ _ hz.le f hv (by linarith)).trans ((mul_le_mul_of_nonneg_right hx hz.le).trans_eq (mul_comm ..)))
   have hr: ‖m i x x-g i x x‖≤ y*u':= (norm_entry (m i-g i) x x).trans (hY i); apply le_trans (norm_le_norm_sub_add (g i x x) (m i x x)); rw [norm_sub_rev]; have ht: (y+z)*u' ≤ e/2:=l; have hs:=norm_le_norm_sub_add (m i x x) (C x x); linarith
 intro i; apply le_trans ((P i).note_n _ b hk (by positivity)); apply Eq.mp _ ((div_le_iff₀ hy).1 (le_max_right (1:ℝ) (c/e))); rw [mul_comm]
#print axioms toured
end Melody
end YM.CF.Buffered.Ballad
