import YM.CF.BProof.Rhythm.Behold
/-! Prebuy B-Gap envelope in advance of h. All remaining y delays taken after this;
work for any Porch (including for the ∞n grant). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Rhythm
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset Hearth Trek
open RG Wilson Mapping.House Pricing Gates.Stage Gates.Stage.Setup Skye
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{a b l r:ℝ}(F:Spin.Ready j a b l r)
-- choose frame prior d fixing availability.
structure Essence (F:Spin.Ready j a b l r)(u:ℝ) where
 rad : ℝ
 disk:Trek.Disk rad
 pre : Tape.Front F rad
 v : ℝ
 H : Mark.Herald u v
 budget : 2*v≤ pre.limit
lemma buyE (h:1≤j)(v:ℝ)(p:0<v) : Nonempty (Essence F v) := by
 obtain ⟨x,d⟩:= Trek.wish; obtain ⟨d⟩:=d; obtain ⟨g⟩:= Tape.buyFront F h (d.p.trans d.up); obtain ⟨b⟩:= Mark.Herald.buys p (show 0<g.limit/8 from div_pos g.legal (by norm_num)); exact ⟨x,d,g,g.limit/8,b,by linarith only [g.legal]⟩
variable {F}{u:ℝ} (E:Essence F u)(D rₜ:ℕ)
-- ready for aperture. rD upper bound on `win` need. Threshold t,Y from Book. Gap size D.
structure Note where
 stage: Tape.Credit F E.rad D
 clock: Trek.Sized (stage.reach+10) E.H.whole
 postL : rₜ≤clock.blockY
 capH : rateH/(D:ℝ) < E.v
 capX : rateH/(D:ℝ)< E.H.good
 up : rateH*(rateH/clock.stepQ) < E.v
 bound : rateH*2*(rateH/clock.taperW) ≤ E.v
-- any sufficiently large fixed D. Clock allowed to depend on any additional base fixed radii incl after rD.
include E
lemma buildD {d:ℕ}(h:0<d)(hj:1≤j)
 (v:rateH/d < E.v)(k:rateH/d < E.H.good): Nonempty (Note E d rₜ):=by
 obtain ⟨g⟩:=Tape.buyCredit F hj (E.disk.p.le.trans E.disk.up.le) E.disk.lid d h
 have z : ∀ᶠ m:ℕ in atTop,0<m ∧ rateH*(rateH/m)< E.v ∧ rateH*2*(rateH/m) ≤ E.v:=by
   have he:= ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul rateH); rw [mul_zero] at he; have he:Tendsto (fun v:ℕ=> rateH/(v:ℝ)) atTop (𝓝 0):= by simpa [div_eq_mul_inv] using he
   exact (eventually_gt_atTop (0:ℕ)).and (((he.const_mul rateH).eventually (gt_mem_nhds (by simpa using E.H.uf))).and ((he.const_mul (rateH*2)).eventually (ge_mem_nhds (by simpa using E.H.uf)))) -- name classical wrong
 obtain ⟨m,l⟩:= z.exists
 let u:=g.reach+10+m+1+rₜ; let V:Trek.Sized (g.reach+10) E.H.whole:=⟨m,l.1,u,(by unfold u; omega),m,l.1,u+(2*E.H.whole.val+1+m),le_rfl⟩; exact ⟨g,V,(by change _≤u; unfold u; omega),v,k,l.2.1,l.2.2⟩
lemma notes_p(h:1≤ j): ∀ᶠ D:ℕ in atTop,∀ rₜ,Nonempty (Note E D rₜ):=by
 have he:= ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul rateH); rw [mul_zero] at he; have he:Tendsto (fun v:ℕ=> rateH/(v:ℝ)) atTop (𝓝 0):= by simpa [div_eq_mul_inv] using he
 filter_upwards [eventually_gt_atTop (0:ℕ),he.eventually (gt_mem_nhds E.H.uf),he.eventually (gt_mem_nhds E.H.gc)] with D u t v
 exact fun r=> buildD E r u h t v
-- calendar readiness at each stop.
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}(L:Side)(a':ℕ)(Δ:Note E (Gates.gap L a') rₜ)(y:ℝ)
structure Season (d:ℕ) : Prop where
 warm: E.H.Warm (Gates.DP L a' y) y
 arrows : Δ.clock.nearM+10≤d
 long : 20*Δ.clock.nearM+20≤Gates.DP L a' y
 outside : 2*Gates.gap L a' ≤ Gates.DP L a' y
 focal : 6*xm*Lease.wearC S y+rateH/(Gates.gap L a') ≤ E.v
 old : 6*xm*Lease.wearC S y+rateH*(rateH/Δ.clock.stepQ)≤E.v
 fund : 3*xm*Lease.wearC S y+rateH/(Gates.gap L a')≤ E.H.good
 innerp : 2*xm*Lease.wearC S y ≤ Δ.stage.price
 hp : 2*xm*Lease.wearC S y+E.disk.v≤ E.rad
 look {s:Side}(i:Bond s):cd SU.group 1 (mag y i)≤Lease.magC S*aA y
lemma measures(S:Gates.Stage c w R v) (W:ℝ→ℕ)(u:Tendsto W atTop atTop): ∀ᶠ y:ℝ in atTop, Season E rₜ L a' Δ y (W y) (S:=S):=by
 let D:=Gates.gap L a'; let l:=Δ.clock.nearM; have he:= Gates.lengths L a'; let f:=Lease.wearC S; have Hp:= (Lease.wearPL S).limit; have H(b c d:ℝ)(h:c<d) : ∀ᶠ y:ℝ in atTop,b*f y+c≤ d:= ((Hp.const_mul b).add_const c).eventually (ge_mem_nhds (by simpa using h));
 filter_upwards [H _ _ _ Δ.capH,H _ _ _ Δ.up,H _ _ _ Δ.capX, H _ _ _ Δ.stage.pos, H _ _ _ E.disk.up,E.H.grabs _ he, u.eventually_ge_atTop (l+10),he.eventually_ge_atTop (20*l+20),he.eventually_ge_atTop (2*D),Lease.mag_C S] with y h h' j h1 h2 p o e x T -- underscores trigger
 refine ⟨p,o,e,x,h,h',j,?_,h2,T⟩; exact (Eq.trans_le (add_zero _).symm h1)
end YM.CF.BProof.Rhythm
