import YM.CF.Cascade.Start
set_option autoImplicit false
noncomputable section
namespace YM.CF.Cascade
open Function Filter Metric Finset Lattice Wilson Next.Free Bloch Laurent Scroll Precision Exterior Lat Ember Aroma
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker
variable {j t:ℕ}{n c f:Side}{k a b:ℝ}
open Tree SU Font Cube Extra.Iteration Nacre
open Thera Fock Dial Peaks Tulip Paige NormedSpace
open Spire Vault Laic Kennel Rush Fir Branch Tenant
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Push.Uniform Planned.JetPort
variable {X:Air n→Op (Single n)}{J:InJ Slot n}
lemma sinG (e:HoldX id place_x X a b t)(p:J=(love n).symm ∘ X)(k:Site n) : Beacon id a t (fun x=>rook (J x) k) (node (0:Site n)) (0:Air n) (‖(coordL (k:=SpinIdx×Slot)).symm.toContinuousLinearMap‖*((2*b)*Decay a (node (0:Site n)) (node k))):=by
 let Q:= coordL (k:=SpinIdx×Slot); let V:=Decay a (node (0:Site n)) (node k); have he : ContDiffAt ℝ ω J 0:=by rw [p]; let L:= (love n).symm.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap; exact ((L.restrictScalars ℝ).contDiff.contDiffAt.comp _ e.glow)
 have ht:0< V:=Push.Uniform.decay_pos ..; rw [p]; have hu:= e.funds
 let F(x:Air n):=rook (((love n).symm∘ X) x) k
 exact matrix_w (F:=F) (fun i j=> Nacre.tort.mp e.glow _ _) (fun i j=> show Beacon id a t _ _ (0:Air n) ((2*b)* V) from pendant (Nacre.tort.mp e.glow) e.law ((0,i.1),i.2) ((k,j.1),j.2)) (by positivity)
private def rL(x:Site n) := (show Cab Slot n→ₗ[ℝ] Op (coneA Slot) from { toFun:=fun y=>rook y x,map_add':= fun _ _=>rfl,map_smul':=fun _ _=>rfl }).toContinuousLinearMap
private def R':=‖(coordL (k:=SpinIdx×Slot)).symm.toContinuousLinearMap‖
private def W (b a:ℝ)(i:Site n):= R'*((2*b)*Decay a (node (0:Site n)) (node i))
lemma wink {X: Air n→ Op (Single n)}{J:InJ Slot n}(h:HoldX id place_x X a b 2)(p:J=(love n).symm ∘ X) (x: Site n)(i:Site (More n)):
 ‖rook (JD J (Aroma.spur i)) x‖≤ W b a x * Decay a (node (0:Site n)) i ∧ ∀ j: Site (More n),‖rook (JG J (Aroma.spur i) (Aroma.spur j)) x‖ ≤ W b a x * (Decay a (node (0:Site n)) i * Decay a (node (0:Site n)) j):=by
 let L:=rL x; let u:=node (0:Site n)
 have he : ContDiffAt ℝ ω J 0:=by rw [p]; let L:= (love n).symm.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap; exact ((L.restrictScalars ℝ).contDiff.contDiffAt.comp _ h.glow)
 have hp:= sinG h p x; have hx {t:ℕ}(v:Fin t → Site (More n)) : entry (fun y=>rook (J y) x) 0 v=L (iteratedFDeriv ℝ t J 0 (fun i=> Push.Uniform.bolt (v i))):=by unfold Push.Uniform.entry; rw [show (fun y=>rook (J y) x)= L ∘ J from rfl,L.iteratedFDeriv_comp_left he le_top]; rfl
 have AV(i: Site (More n)): Push.Uniform.bolt i= Aroma.spur i := by funext j; by_cases h:i=j<;>simp [Push.Uniform.bolt,Aroma.spur,h,Ne.symm]
 constructor
 · have ht:= hp 1 (by norm_num) (fun _=>i); rw [hx] at ht; simp only [spanSites,id_eq,sum_const,card_univ,Fintype.card_fin, Nat.cast_one,nsmul_eq_mul,one_mul,iteratedFDeriv_one_apply, AV] at ht; convert ht <;> first|rfl|simp [Decay]
 intro j; let v:Fin 2→ Site (More n):=![i,j]; have ht:=hp 2 le_rfl v; rw [hx] at ht; simp only [spanSites,Fin.sum_univ_two, v,id_eq,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one, iteratedFDeriv_two_apply,AV] at ht; have he':W b a x * Real.exp (-a * (↑(separation u i + separation u j):ℝ)) ≤ W b a x * (Decay a u i * Decay a u j):=by unfold Decay; rw [←Real.exp_add,Nat.cast_add,mul_add]
 exact he'.trans' ht
lemma banks(x:Site n): sand (lift x)≤4*separation 0 x:=by unfold sand; refine (sum_le_sum (g:=fun _=> (↑(separation 0 x):ℝ)) ?_).trans_eq ?_; intro i _; rw [separation_comm,separation,sub_zero]; exact_mod_cast component_le ..; rw [sum_const,card_univ, nsmul_eq_mul]; rfl
lemma verse(k:Site n):separation (node (0:Site n)) (node k)= 2*separation 0 k:=by unfold node; rw [separation_translate]; exact emptio (assembly n) 0 k
lemma verse0 : separation 0 (node (0:Site n))≤1:=by
 rw [show node (0:Site n)=1 from ?_]; swap; · unfold node; simp; exact (assembly n).root.map_zero
 have hp:(1:Site (More n))=wrap _ (1:Cover):=by funext i; change 1=((1:ℤ):Per (More n)); norm_num
 rw [separation_comm,separation,sub_zero,hp]; refine Work.E01.pdist_wrap_le ?_; rw [box_test]; exact ⟨fun i=> by change (-↑(1:ℕ):ℤ)≤1; norm_num,fun i=>by change (1:ℤ)≤ (↑(1:ℕ):ℤ); norm_num⟩
lemma sow(h:0<a)(x:Site (More n)): idea (a/8) x * Decay a (node (0: Site n)) x≤Real.exp (a/2)*Decay (a/2) (node (0:Site n)) x:=by
 let v:=node (0:Site n)
 have he: (separation 0 x:ℝ)≤ 1+↑(separation v x):=by exact_mod_cast ((separation_triangle (0:Site (More n)) v x).trans (add_le_add_left verse0 _)) -- left/right
 unfold idea Decay; simp only [← Real.exp_add]; apply Real.exp_monotone; apply le_trans (add_le_add_left (mul_le_mul_of_nonneg_left (banks x) (show 0≤a/8 from by positivity)) _)
 nlinarith only [h,he,mul_le_mul_of_nonneg_left he h.le]
lemma story (h:0<a)(x:Site n): idea (a/8) x*Decay a (node (0:Site n)) (node x)≤Decay (a/2) 0 x:=by unfold idea Decay; rw [←Real.exp_add,verse]; apply Real.exp_monotone; push_cast; nlinarith only [banks x,mul_le_mul_of_nonneg_left (banks x) h.le,mul_nonneg h.le (show 0≤ (separation 0 x:ℝ) by positivity)]
lemma Bird (a b:ℝ)(p:0<a)(k:0<b): ∃ C:ℝ,0<C∧∀ {n:Side}{X:Air n→Op (Single n)}{J:InJ Slot n},HoldX id place_x X a b 2 → J=(love n).symm ∘ X → Aroma.bill J (a/8)≤ C ∧ Aroma.b2 J (a/8) ≤ C:=by
 let L:=Real.exp (a/2); let d:=countCost (a/2); have ha:= half_pos p; have hx:0<L:=Real.exp_pos _; have hp:0<d:=count_pos ha; have hv:0≤ R':=norm_nonneg _; let V:= R'*(2*b); have hV:0≤V:=by positivity
 let B:=V*d*(L*d); let A:=B*(L*d); have hB: 0≤ B:=by positivity
 have hA:0≤A:=by positivity
 refine ⟨1+B+A,by positivity,fun {n X J} H q=>?_⟩
 let z:=a/8; let D(i: Site n):= idea z i *W b a i; let F(x:Site (More n)):= idea z x* Decay a (node (0:Site n)) x
 have he: ∑ i,D i≤ V*d:=by
    refine le_trans (sum_le_sum (g:=fun k: Site n=> V * Decay (a/2) 0 k) ?_) ?_; intro i _; unfold D W; refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (story p i) hV); unfold z V; ring
    rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (decay_count ha (0:Site n)) hV
 have ht:∑ x:Site (More n),F x ≤ L*d:=by apply le_trans (sum_le_sum (fun i _=> sow p i)); rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (decay_count ha _) hx.le
 have hh:0≤∑ i:Site (More n),F i:=sum_nonneg fun i _=>mul_nonneg (Real.exp_pos _).le (Push.Uniform.decay_pos ..).le
 constructor
 · apply le_trans (b:=B) _ (by linarith); apply le_trans _ (mul_le_mul he ht hh (mul_nonneg hV hp.le)); unfold D F Aroma.bill; simp_rw [sum_mul,mul_sum]; refine sum_le_sum fun i _=>sum_le_sum fun j _=>?_ ; exact (mul_le_mul_of_nonneg_left (wink H q i j|>.1) (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le))).trans_eq (by simp only [z,idea]; ring)
 apply le_trans (b:=A) _ (by linarith); apply le_trans _ (mul_le_mul (mul_le_mul he ht hh (mul_nonneg hV hp.le)) ht hh hB); unfold D F Aroma.b2; simp_rw [sum_mul,mul_sum,sum_mul]; refine sum_le_sum fun i _=>sum_le_sum fun j _=> sum_le_sum fun k _=>?_ ; exact (mul_le_mul_of_nonneg_left (wink H q i j|>.2 k) (mul_nonneg (mul_nonneg (Real.exp_pos _|>.le) (Real.exp_pos _|>.le)) (Real.exp_pos _|>.le))).trans_eq (by simp only [z,idea]; ring)
end YM.CF.Cascade
