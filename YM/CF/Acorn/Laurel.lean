import YM.CF.Acorn.Violet
set_option autoImplicit false
noncomputable section
namespace YM.CF.Acorn
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush Matrix Jet
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L B:Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m:Side}(g:Grasp Y B e)(n:ℕ)(K:ℝ)(S:Broc.Table m B)
lemma up_arm(n:ℕ)(u a w c r z:ℝ)(hu:0<u)(ha:0<a)(hw:0≤w)(hc:0≤c)(hr:0≤r)(hz:0<z): ∃ v:ℝ,0<v∧∀ k d:ℕ,0<k→ (d:ℝ)≤ z*k→∀ h:ℝ,1≤h→ u*Real.exp (a*d)*treasure a h w c r d n ≤ Real.exp (v*k*h^2):=by
 let b:= worth n; have hb:b>0:=zero_lt_one.trans_le (one_w n)
 let x:=b*(2*r)+6*b*(2*c)* b^2*(Real.exp a+(w+w))^2+ 6*b*(2*w)*b^2*(Real.exp a+(w+w))^2
 let y:=u*b^2; let V:= a*z+y+x*z; have hy:0<y:=by unfold y; positivity
 have hj:0≤x:=by unfold x; positivity
 refine ⟨V,by unfold V; positivity,fun k d g p h l=> ?_⟩
 let X:=b*(d*(2*r)); let Y:=b*(6*DriftX a h (w+w) (d*(2*c)) n); let Z:=3*(b*(2*DriftX a h (w+w) (d*(2*w)) n)); let W:= X+Y+Z
 have he:1 ≤ h^2:= one_le_pow₀ l; have hp:1≤(k:ℝ):=by exact_mod_cast g
 have hg: W≤ x*(d*h^2):=by unfold W X Y Z x DriftX b; nlinarith [mul_le_mul_of_nonneg_left he (show 0≤ worth n*(d*(2*r)) from mul_nonneg hb.le (by positivity))] -- tune
 unfold treasure
 calc
   _ = y*Real.exp ((a*d)+W):=by unfold y W X Y Z b; simp only [Real.exp_add]; ring
   _ ≤ Real.exp (y+(a*d+W)):=by rw [Real.exp_add y]; gcongr; linarith [Real.add_one_le_exp y]
   _ ≤ _:= by
     apply Real.exp_le_exp.mpr; apply le_trans (add_le_add_right (add_le_add (mul_le_mul_of_nonneg_left p ha.le) (hg.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p (by positivity)) hj))) y) _ -- y right? add names
     unfold V; nlinarith [mul_le_mul_of_nonneg_left he hy.le,mul_le_mul_of_nonneg_left hp (show 0≤ y*h^2 by positivity),mul_le_mul_of_nonneg_left he (show 0≤ a*z*k by positivity)]
theorem compareX (hK:1≤K)(R:Repair j)(p:e ≤ R.d)(l:g.baseline≤ R.d) : ∃ a v:ℝ,0<a ∧ 0<v∧∀ m:Side,R.n≤(CSide m B).val→g.roundZ≤(CSide m B).val→∀ M:Male,∀ S:Broc.Table m B,Grove (terr _) S→∀ z:ℝ,1≤z→ ∃ A:Castle m B e S→FC (Iota (idrat (CSide m B))), (∀ x,acts (A x) (neat g m M (x.val false)) = neat g m M (x.val true)) ∧ Carries (landX n K S e) (tempo (idrat (CSide m B)) 1).home S a z A (Real.exp (v*S.card*z^2)):=by
 -- strengthen later with h
 obtain ⟨u,H,P⟩:=boil_x g n K hK
 obtain ⟨C,D,c,d,Q⟩:= burst g n u R p l H
 let a:=billV g R; have ha:= billVP g R
 obtain ⟨w,hw,M⟩:=played (B:=B) (e:=e) n K hK
 obtain ⟨s,hs,L⟩:= gather_v B a ha w hw n
 obtain ⟨v,hv,Y⟩:= up_arm n s a (4*C) C D (feeG (8*B.val)) hs ha (by positivity) c d (by unfold feeG; positivity)
 have hp:0<rateC a B/2:=by unfold rateC feeG; unfold a; positivity
 refine ⟨_,v,hp,hv,fun m k t M' S h z wz=>?_⟩
 let x:=tentX m B S; have hx:S.Nonempty:=by cases h <;> simp
 obtain ⟨F,H⟩:=Q m k t M'
 obtain ⟨A,f,o⟩:=budget_delta (h:=z) (v:=grove_foam S h) (hx.mono (foam_in ..)) (P _ _ false) (P _ _ true) (silentX g n S u) ha.le (zero_le_one.trans wz) H -- tune args
 obtain ⟨G,e',T⟩:=save_x n K S ha (zero_le_one.trans wz) (M m S) hs.le (L m) f (F:=fun x=> neat g m M' (x.val false)) (G:=fun x=> neat g m M' (x.val true)) o
 exact ⟨G,T,e'.more (Y S.card x.card (Finset.card_pos.mpr hx) (raise_foam _ h) z wz)⟩
end YM.CF.Acorn
