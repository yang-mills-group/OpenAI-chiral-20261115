import YM.CF.Summit.Pils
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Center
set_option autoImplicit false
noncomputable section
namespace YM.CF.Summit
open Function Filter Set Matrix MeasureTheory FreeResolvent TestD AnalyticBridge.RelativeLogdet Differential Ink AnalyticBridge.SectorAffine Lattice Wilson RG Precision Pressure Tree Exterior
open Next.SectorChange (shots panels)
open Next.SectorChange.Schur (principal)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {ι X E τ : Type}[Fintype ι][DecidableEq ι][NormedAddCommGroup E][NormedSpace ℝ E]
 {W:Mark τ X}{D:Cost X}{v:τ→E}{p:ι→ X}{x:E}{A K F:E→Square ι}{I:ι→Set ι}{α σ r C d u Y N b B:ℝ}{n:ℕ}
lemma unit_rice (k:Bundle v W D p p F x n σ C)(T:Bundle v W D p p A x n σ C)(h:Bundle v W D p p K x n σ C)(w: Bundle v W D p p (fun u => K u - F u) x n σ (b*C)) (s:∀ᶠ y in 𝓝 x,(F y).transpose*A y*F y=1)(hc:0≤C)(hb:0≤b)(hd:0 ≤ d)(ht:0 ≤ u)(he:d+2*n*u ≤ σ)(p':W.Move D u 1):
 let M := tagPrice 1 n (tagPrice 1 n C C) C
 Bundle v W D p p (fun y=>(K y).transpose*A y*K y-1) x n d ((M+M)*b):=by
 intro M; let a :ℝ:= d+n*u; let δ := mul_nonneg hb hc; have ha:0≤a:= by unfold a; positivity
 have hm:a+n*u≤σ:=by unfold a; linarith
 have hl:a ≤ σ:=le_trans (le_add_of_nonneg_right (show 0≤(n:ℝ)*u by positivity)) hm
 have hk:= (w.transpose.multiply T p' ht le_rfl δ hc ha hm).multiply (h.mono hl le_rfl) p' ht le_rfl (tag_poss le_rfl δ hc n) hc hd le_rfl
 have hp:= (k.transpose.multiply T p' ht le_rfl hc hc ha hm).multiply (w.mono hl le_rfl) p' ht le_rfl (tag_poss le_rfl hc hc n) δ hd le_rfl
 apply ((hk.one_add hp).mono le_rfl (le_of_eq (by unfold M tagPrice; ring))).glue; filter_upwards [s] with y hy
 rw [transpose_sub,Matrix.sub_mul,Matrix.sub_mul,Matrix.mul_sub,hy]; abel
lemma rice_s(k:Bundle v W D p p F x n σ C)(w:Bundle v W D p p (fun y=>K y-F y) x n σ d): Bundle v W D p p K x n σ (d+C):=by
 apply (w.one_add k).glue; exact Eventually.of_forall fun y=> sub_add_cancel ..
section permit
variable {G:Gauge} {c f:Side}
open YM.Next.SectorChange.Rows (gram move)
abbrev bark {S:StepData c f}(x:ℝ)(V:Config G c)(T:Tube G S)(k:S.Choices)(A:Stores S)(F:Forest S.ratio) := mild (panels A F) (gram T x V k (shots S x) A F)
abbrev musk {S:StepData c f}(x:ℝ)(V:Config G c)(T:Tube G S)(k:S.Choices)(A:Stores S)(F:Forest S.ratio) :=(bark x V T k A F).transpose*gram T x V k (shots S x) A F*bark x V T k A F-1
def Credit {n:ℕ} (G:Gauge)(T: Teller G)(S: RG.Patch)(x a d v C m:ℝ):Prop:= ∀ {c f:Side}(V:StepData c f)(U:Tube G V),V.patch=S →100*(1+radiusB x)≤c.val→ Teller.Funds T V U → ∀ (A: Stores V) (F:Forest V.ratio)(k:V.Choices)(P:Config G c),A.flags=RG.flags (temp x) P→∀ B:PriceCoords G c, ‖B‖≤a→
 let p:= Next.SectorChange.Wisps.front A F (x:=x) (G:=G)
 let K:=fun z:PriceCoords G c=>gram U x (field P z) k (shots V x) A F
 let H:=fun z:PriceCoords G c=> bark x (field P z) U k A F
 Gap (K B) m ∧ Polar B p p K n d C ∧ Polar B p p H n d C ∧ Polar B p p (fun z=>musk x (field P z) U k A F) n d (C*Real.exp (-v* (radiusB x/60:ℕ)))
lemma stampX (n:ℕ)(G:Gauge)(T:Teller G)(S: RG.Patch)(ht:S.Branches T.bind G):∃ a d v C m:ℝ,0<a∧0<d ∧ 0<v ∧0<C ∧0<m ∧∀ᶠ x in atTop,Credit (n:=n) G T S x a d v C m:=by
 obtain ⟨r,d0,u,m,l,M,hr,h0,hu,hm,hl,hM,h⟩:= estimates G S T ht n; let R:= room d0 (M+1) (min m 1 / 2) n
 have hY : 0<min m 1 / 2:= half_pos (lt_min hm zero_lt_one); have hp:0 ≤ M+1:= by positivity
 let V:=priceFiber S G R; let X: Price d0 (M+1) (min m 1/2) R 1 V 1 n := ⟨hY,hp,h0,rfl,le_rfl,(priceFiber_pos ..).le,zero_le_one,le_rfl⟩
 let Q:= meter n n (M+1) 1 (rise V (min m 1 /2)); let F:= (2/Real.pi)*Q
 have hf:0<R:= X.pos; have hq:0≤Q:= X.meter_abs; have hF:0≤F:=by unfold F; positivity
 let O:= (2/Real.pi)*tagPrice 1 n Q (tagPrice 1 n (M+1) (V*Q)); have ho : 0≤O := by unfold O; exact mul_nonneg (by positivity) (Differential.tag_poss le_rfl hq (Differential.tag_poss le_rfl hp (mul_nonneg X.vol hq) n) n)
 let w := M+F+O; let C:=w+(tagPrice 1 n (tagPrice 1 n w w) w+tagPrice 1 n (tagPrice 1 n w w) w)
 have hw:0<w:=by unfold w; linarith
 have hC:w ≤ C := le_add_of_nonneg_right (add_nonneg (tag_poss le_rfl (tag_poss le_rfl hw.le hw.le n) hw.le n) (tag_poss le_rfl (tag_poss le_rfl hw.le hw.le n) hw.le n))
 let d:= R/(2*n+1); let v:= (n+1:ℕ)*R; have hd:0<d:=by unfold d; positivity
 have hv:0<v:=by unfold v; positivity
 have ha:R ≤ d0:=room_small X
 have hh:d+2*n*d ≤ R:=by unfold d; field_simp; nlinarith
 have hT:d ≤ R:=le_trans (le_add_of_nonneg_right (by positivity)) hh
 refine ⟨r,d,v,C,m,hr,hd,hv,hw.trans_le hC,hm,?_⟩
 filter_upwards [h] with x hx
 intro c f S' U hL hi hP A F' k P he B hB p K H
 have hg := hx.2 S' U hL hi hP A F' P he k B hB
 have h' := hg.solvency; have hX: (native c).Volume p R V:=by unfold V; rw [← hL]; exact (fiber_volume S' G hf A F' x).1
 let I:=panels (x:=x) A F' (G:=G); have H':= Next.SectorChange.boards A F' G hx.1; let b:=Real.exp (-v*(radiusB x /60:ℕ)); have hy : 0 ≤ b:= Real.exp_nonneg _
 obtain ⟨j,t⟩:= pole_run I (Polar.toBundle hg.gramJets ha) h' hm hM.le X hX (Mark.position_move (native c) _ hf.le) (Next.SectorChange.Schur.per_self H') (shipment_near H')
 have hk: Polar B p p (fun s => shard (K s)) n R F:=j; have ht : Polar B p p (fun s=> H s-shard (K s)) n R (b*O):=by
    unfold b v; rw [← neg_mul ↑(n+1:ℕ) R]; exact t
 have hO : M ≤ w:=by unfold w; linarith
 have hΔ : b*O + F ≤ w:= by
    have ht : b ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)); unfold w; nlinarith only [ht,hM,ho]
 have hw' : Polar B p p H n R w:= (rice_s hk ht).mono le_rfl hΔ
 refine ⟨h', thin hg.gramJets le_rfl (hT.trans ha) (hO.trans hC), thin hw' le_rfl hT hC,?_⟩
 have he : ∀ᶠ y:PriceCoords G c in 𝓝 B,(shard (K y)).transpose*K y*shard (K y)=1:=by
    apply Eventually.mono (presses (price_knowledge hg.gramJets le_rfl h') hm (Eventually.of_forall fun z=> (isHermitian_iff_isSymm.mpr (show (K z).IsSymm by unfold K Next.SectorChange.Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul, Matrix.transpose_transpose])))) fun z hz=> shard_unit hz
 exact (unit_rice (Polar.toBundle (hk.mono le_rfl (show F ≤ w by unfold w; linarith)) hT) (Polar.toBundle (thin hg.gramJets le_rfl ha hO) hT) (Polar.toBundle hw' hT) (Polar.toBundle (B:=B) (ht.mono le_rfl (mul_le_mul_of_nonneg_left (show O ≤ w by unfold w; linarith) hy)) hT) he hw.le hy hd.le hd.le hh (Mark.position_move (native c) _ hd.le)).mono le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hw.le) hy)
end permit
end YM.CF.Summit
