import ForceSatin.ExactShear
import YM.SU5.Relativistic.Succot
import YM.SU5.Lamour.Ferry
-- Adapt Nero (toes,gift) proof to pass two-variable joint untruncated limits at the Lane.
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Set Filter NormedSpace Fock Finset Thera MeasureTheory Metric Lattice Cube Lat Fir Onyx Rush Ember SU Scroll Skye Tulip BPress.Spin.Blank Flare
open Laurent Bloch Dial Jill Crest Crest.Shore Crest.Sleet Buffered Emu Lifted Loaves Verses
open Lamour
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder NNReal ENNReal Kronecker
attribute [local instance] opCStarAlgebra

private lemma slog (L:List Bite) (ε:ℝ)(p:0<ε):∀ᶠ k:ℕ in atTop,∀ (N:Side)(M:Jill.Male),IsStarProjection (spar 4 M (1:Pane N))→∀ v:ℕ,k ≤ v→ ‖earnK (N:=N) M v L-earnK (N:=N) M k L‖≤ε:=by
 obtain ⟨C,g,h⟩:=stilt_h; let q:=1+C; let l:=L.length; let D:=(l+1:ℝ)*q^l; let δ:=ε/D; have ht:1 ≤ q:=le_add_of_nonneg_right g.le; have hD:0<D:=by unfold D; positivity
 have hδ:0<δ:=div_pos p hD
 filter_upwards [stilt_p hδ] with k H N M p' v a
 let P:=spar 4 M (1:Pane N); let F(i:ℕ):Bite→Reader0 (Single N):= stilt i P; obtain ⟨x,b⟩:=phoz p'; rw [bandN v _ p' x b,bandN k _ p' x b,stamps, stamps, ←inner_sub_right,←act_sub]
 let G(i:ℕ):=ton∘F i; apply le_trans (pike_cross _ x b.2)
 have hu(i:ℕ)(j:Bite): ‖G i j‖ ≤ q:= by apply (cost_pe ..).trans; exact (h N M p' i j).trans (le_add_of_nonneg_left zero_le_one)
 apply (normsDiff (G v) (G k) q ht δ hδ.le L (fun i _=> hu ..) (fun i _=> hu ..) (fun i _=>(scone i.hand _ _).trans (H N M p' v a i))).trans
 conv_rhs => rw [← div_mul_cancel₀ ε hD.ne']
 change (l:ℝ)*δ*q^l≤δ*D
 have hf:0<q^l:=by positivity
 unfold D; nlinarith only [mul_nonneg hδ.le hf.le]
lemma trueMean (L:List Bite) (ε:ℝ)(pε:0<ε):∃ n:ℕ,∀ (N:Side)(M:Jill.Male),n ≤ N.val → n≤M.val.val→ Even N.val → IsStarProjection (spar 4 M (1:Pane N))→∀ q:Wave _, Sea (spar 4 M (1:Pane N)) q → ‖alleyR (mateK N) q (chartP N L)-zTariff L‖ ≤ ε:=by
 obtain ⟨k,h,q⟩:= ((slog L _ (half_pos pε)).and (gift L _ (half_pos pε))).exists; obtain ⟨b,q⟩:= q
 refine ⟨b,fun N M e g v p u t=>?_⟩
 let G:=chartP N L; let P:=FlatPaneP 4 M N; let U:= exactShear 4 M N (by decide) p; let V(x:ℕ):= Saber (B:=tickA N) p x
 let X:=alleyR (mateK N) u G; let W(k':ℕ):= earnK (N:=N) M k' L
 have he:Tendsto W atTop (𝓝 X):=by
   let F(z: Op (Single N) × Op (Single N)):=inner ℂ u (acts (quant z.1*G*quant z.2) u)
   have hf:Continuous F:=by unfold F; fun_prop
   rw [show X= F (U.sell,U.buy) from (Eq.trans (by change (inner ℂ (mateK N) u)⁻¹*inner ℂ (mateK N) (acts G u)=inner ℂ (mateK N) (acts G u)/inner ℂ (mateK N) u; rw [div_eq_mul_inv,mul_comm]) (flat_price 4 M N _ p _ t (tickB N)))]
   exact ((hf.tendsto (U.sell,U.buy)).comp ((shear_sell_tends 4 M N _ p).prodMk_nhds (shear_buy_tends 4 M N _ p))).congr (fun x=> (bandN x L p u t).symm)
 change ‖X-zTariff L‖≤_
 have hv:‖X-W k‖≤ ε/2:=le_of_tendsto (he.sub_const (W k)|>.norm) ((eventually_ge_atTop k).mono (fun i e=>h N M p i e))
 rw [show X-zTariff L=X-W k+(W k-zTariff L) by abel]; exact (norm_add_le ..).trans ((add_le_add hv (q _ e v _ g p)).trans_eq (add_halves _))

lemma trueWine (L:List Wine) (ε:ℝ)(pε:0<ε):∃ n:ℕ,∀ (N:Side)(M:Jill.Male),n ≤ N.val → n≤M.val.val→ Even N.val → IsStarProjection (spar 4 M (1:Pane N))→∀ q:Wave _, Sea (spar 4 M (1:Pane N)) q → ‖alleyR (mateK N) q (motet N L (1,1))-tallyW L‖ ≤ ε:=by
 induction L generalizing ε with
 | nil=> exact ⟨0,fun _ _ _ _ _ _ _ _=>by simpa [motet,tallyW] using pε.le⟩
 | cons i L ih=>
    let y:=‖i.fees 1‖+1; have hy:0<y:=by unfold y; positivity
    let v:= ε/(2*y); have hv:0<v:=by unfold v; positivity
    obtain ⟨p,u⟩:= trueMean i.song _ hv; obtain ⟨q,w⟩:=ih _ (half_pos pε)
    refine ⟨max p q,fun N M g l a h d t=>?_⟩; let F:= alleyR (mateK N) d; let x:= i.fees 1
    have he : motet N (i::L) (1,1)=x • chartP N i.song +motet N L (1,1):=by simp [motet,x,pulseX, (show onC N (1:Pane N)=1 from funext (fun x=> onC_spec ..))]
    rw [he,map_add,map_smul,smul_eq_mul]; change ‖x*F (chartP N i.song)+F _ - (x*zTariff i.song + tallyW L)‖ ≤ ε
    rw [show x* _+F _-(_+tallyW L)=x*(F (chartP N i.song)-zTariff i.song)+(F (motet N L (1,1))-tallyW L) from (?_)]; swap; · ring -- holes trouble
    apply (norm_add_le ..).trans; rw [norm_mul]; apply (add_le_add (mul_le_mul (show ‖x‖≤y from le_add_of_nonneg_right zero_le_one) (u N M (by omega) (by omega) a h d t) (norm_nonneg _) hy.le) (w N M (by omega) (by omega) a h d t)).trans_eq; unfold v; field_simp; norm_num
#print axioms trueWine
end YM.CF.Papyrus.Franc.SatinForce
