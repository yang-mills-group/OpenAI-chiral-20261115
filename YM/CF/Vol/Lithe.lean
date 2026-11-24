import YM.CF.Vol.Wage
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vol
open Function Filter Set Matrix Lattice Wilson RG Precision Pressure Tree Exterior MeasureTheory Metric
 AnalyticBridge.MarginalMultiplier3b1d AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine Char Newt
open Push.SectorMeasure AnalyticBridge.RelativeLogdet.Ink
open Push Push.Uniform Hors Finset Laurent Bloch
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {P:RG.Patch}{G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{K:Teller G}{F:Forest S.ratio}{X E B:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup B][NormedSpace ℝ B]{t x s D A C Q V r:ℝ}{i n l:ℕ}
-- gap vectors, direct Wilson discrepancy, analytic-through neighborhoods.
open Tube Next.Fluctuations
section features
variable (R:ℕ)(U:Config G f)(V:Config G c)(T:Tube G S)(k:S.Choices)
def sore(P:Gauge)(v:P.El):ℝ:= P.price v-‖P.curvature v‖^2/2
def RiftF:=fun i: Twin f=>T.Xf R U i - zip (T.Φ R V) (T.Xn R V) i
def RiftI:=fun i: Bond c=> Z S (S.prediction U k) V i -zip (T.Φ' R V) (T.Xn R V) i
def RiftN:=zip (T.N R V) (T.Xn R V)
def RiftL:=lGap T R U (S.prediction U k) V
def RiftD:=dGap T R V (T.Xn R V)
def KissP:=fun i:Cell f=>T.high.direct*sore G (faceValue U i)
def KissQ:=fun i:Cell c=>T.low.direct*sore G (faceValue V i)
def KissI:=fun i:Bond c=> S.kernel.penalty*sore G (tideX S k V U i)
end features
structure Marble (n:ℕ)(T:Tube G S)(U:E → Config G f)(V:E → Config G c)(k:S.Choices)(R:ℕ)(x:E)(C:ℝ): Prop where
 roof(i:Twin f): Allows n (fun y=>RiftF R (U y) (V y) T i) x C
 jamb(i:Bond c): Allows n (fun y=>RiftI R (U y) (V y) T k i) x C
 letup(i: Twin c): Allows n (fun y=> RiftL R (U y) (V y) T k i) x C
 dPole(i: Twin c):Allows n (fun y=> RiftD R (V y) T i) x C
 nPole i:Allows n (fun y=>RiftN R (V y) T i) x C
 pays(i:Twin c):Allows n (fun y=>T.Xn R (V y) i) x C
 S f: Allows n (fun y=>KissP (U y) T f) x C
 Q c: Allows n (fun y=>KissQ (V y) T c) x C
 I i: Allows n (fun y=>KissI (U y) (V y) k i) x C -- tune arguments order
lemma minusx {E F: Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]{x:E}{f g:E→F} (h:Allows n f x C)(p:Allows n g x D):Allows n (fun y=> f y-g y) x (C+D):=by have he:=h.add (p.smul (-1)); simpa only [neg_one_smul,abs_neg,abs_one,one_mul,←sub_eq_add_neg] using he
lemma sorePrice(G:Gauge)(C:ℝ)(n:ℕ) : ∃ M:ℝ,0 < M ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](U:E→ G.El)(x:E), Allows n (fun y=> G.mat (U y)) x C → Allows n (fun y=> sore G (U y)) x M:=by
 let L:= curvatureCost G*C
 obtain ⟨Z,h⟩:= Uniform.square_pay G n 1 1 1 -- uses rootsCost wrong L. use exists_allows
 obtain ⟨D,hD,hX⟩:= exists_allows (isCompact_closedBall (0:G.Color) L) (fun i (_ : i∈closedBall (0:G.Color) L)=> ((contDiff_norm_sq (𝕜:=ℝ) (E:=G.Color) (n:=ω)).div_const 2).contDiffAt (x:=i)) n
 refine ⟨max (priceCost G C+Uniform.composeCost n D L) 1,lt_of_lt_of_le zero_lt_one (le_max_right ..),fun U x h=>?_⟩ -- tune binder
 have hv:= curvature_price (G:=G) h; have hw:= hX _ (mem_closedBall_zero_iff.mpr hv.value); exact (minusx h.price (hw.comp (f:=fun z=> G.curvature (U z)) hv)).mono (le_max_left ..)
lemma drops (K:Teller G)(L:Side)(n:ℕ)(C M:ℝ)(p:PaintSupply G n D)(h:‖(1:G.Mat)‖ ≤ C):∃ V:ℝ,0<V∧∀ {c f:Side}(S:StepData c f)(T:Tube G S), K.Funds S T→ S.patch.L=L→∀{E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E](U:E → Config G f)(V':E → Config G c)(x:E)(k:S.Choices),paysX n U V' x M C k →∀ r:ℕ, Marble n T U V' k r x V:=by
 have he:0≤ C:=(norm_nonneg _).trans h; obtain ⟨N,y,hN,-,h1⟩:= shortened K.top.clip K.top.paths K.top.width_pos p he; obtain ⟨N',z,hN',-,h2⟩:= shortened K.below.clip K.below.paths K.below.width_pos p he
 obtain ⟨X,hX,hv⟩:= avoids K L C h n; let Z':= Real.sqrt K.bind.penalty * (curvatureCost G * M); let Z:=max 1 Z'; have hz:0<Z:=lt_of_lt_of_le zero_lt_one (le_max_left ..); obtain ⟨E,hE,hW⟩:=sorePrice G (travelCost G n 4 C) n; obtain ⟨e,he,hg⟩:=sorePrice G M n
 let V:= N + X*N' + Z + X*N + X*Z + N'+ N'+ X*N' + X*(X*N')*3 + X*N'+ K.top.clip.direct*E+K.below.clip.direct*E+ K.bind.penalty * e
 have hf:=K.top.clip.quadratic_pos; have ht:=K.below.clip.quadratic_pos; have hp:=K.bind.penalty_pos
 refine ⟨V, by unfold V; positivity,?_⟩; intro c f S T h hL E' _ _ U Q x k H r
 obtain ⟨C',D',hH,hG⟩:= h.feeds; obtain ⟨hu,hw,hl⟩ := H; have hP(i):Allows n (fun y=> T.Xf r (U y) i) x N:=by unfold Xf; rw [h.high]; exact h1 U x hw T.up hH r 1 (by decide) _
 have hQ(i):Allows n (fun y=> T.Xn r (Q y) i) x N':=by unfold Xn; rw [h.low]; exact h2 Q x hl T.down hG r S.patch.L.val S.patch.L.property _
 have hZ(i):Allows n (fun y=> Tube.Z S (S.prediction (U y) k) (Q y) i) x Z:=by
    unfold Tube.Z; rw [h.knobs]; refine ((curvature_price (U:=fun y=>tideX S k (Q y) (U y) i) (hu i)).smul _).mono (le_trans (le_of_eq ?_) (le_max_right ..)); rw [abs_of_pos (Real.sqrt_pos.mpr hp)]
 obtain ⟨h1,h2,h3⟩:=hv Q x hl S hL T h r
 let P(i:Twin c):=hQ i; have h₁:= h1.1 _ _ hN'.le hQ; have h₂:= h2.1 _ _ hN'.le hQ; have h₃:= h3.1 _ _ hN'.le hQ; have hV:0≤ X*N':=mul_nonneg hX.le hN'.le
 have hz':0≤ X*(X*N'):=by positivity
 have hM:0≤ K.top.clip.direct*E:=by positivity
 have hM':0≤ K.below.clip.direct*E:=by positivity
 have hX':0≤ K.bind.penalty*e:=by positivity
 have hY:0≤ X*N:=by positivity
 have hk:0 ≤ X*Z:=by positivity
 constructor
 · intro i; exact (minusx (hP i) (h₁ i)).mono (by unfold V; linarith)
 · intro i; exact (minusx (hZ i) (h₂ i)).mono (by unfold V; linarith)
 · intro i; exact (minusx ((h1.2 _ _ hN.le hP i).add (h2.2 _ _ hz.le hZ i)) (hQ i)).mono (by unfold V; linarith)
 · intro i; exact (minusx (hQ i) (((h1.2 _ _ hV h₁ i).add (h2.2 _ _ hV h₂ i)).add (h3.2 _ _ hV h₃ i))).mono (by unfold V; linarith)
 · intro i; exact (h₃ i).mono (by unfold V; linarith)
 · intro i; exact (hQ i).mono (by unfold V; linarith)
 · intro i; unfold KissP; rw [h.high]; exact ((hW _ _ (travel_jets (U:=U) hw _ (w:=square i.2.val.1 i.2.val.2) (a:=4) le_rfl)).smul _).mono (by rw [abs_of_pos hf]; unfold V; linarith)
 · intro i; unfold KissQ; rw [h.low]; exact ((hW _ _ (travel_jets (U:=Q) hl _ (w:=square i.2.val.1 i.2.val.2) (a:=4) le_rfl)).smul _).mono (by rw [abs_of_pos ht]; unfold V; linarith)
 intro i; unfold KissI; rw [h.knobs]; exact ((hg _ _ (hu i)).smul _).mono (by rw [abs_of_pos hp]; unfold V; linarith)
end YM.CF.Vol
