import YM.SU5.Reconstruction.Cashier.Reserve
/-! Saturated-lines Euclidean budget. Proof variant of PairedProtocol.winePair. -/
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
open Pannier
local notation "G🌸"=> SU.group
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
namespace Papal
open Buffered Afterglow Journey
open scoped ComplexOrder
open CF.Pannier.Chancel
open CF.Pannier.Chancel.Cliplet
variable (H:Real.exp 1≤ P.x)
variable {A δ ε γ h R κ e a:ℝ} {w d t q l0:ℕ} -- λ' inner
local notation "κI" i:max s:max k:max => (gram Y s i k).J.M
local notation "SN" i:max s:max => Papal.count Y s i
private lemma tenderPack(s i k:ℕ)(f:Ferry Y s i k): Twosome (tent Y H) (Papal.count Y s i) (solder Y i k f.depth s):=by
 let m:=momentm Y i s; let K₀:=tent Y H; let X:=collector Y H i k f.depth s; let F:=solder Y i k f.depth s; have ht:=boxprice Y H i k f.depth s f.fire f.enters
 apply across K₀ m F (terrain Y H (Y.ir i) s) (Y:=X) (fun x=>rfl); exact fun a z _ p=>Metered.twiceX ht a z p
where across (K:Calibration)(m:Side){n:Side} (X:Mark n→ℂ)(p:K.c m=n){Y:Mark (K.c m)→ℂ}(h:∀ f,Y f=X (p▸f)) (g:Twosome K (K.c m) Y):Twosome K n X:=by subst n; rw [show X=Y from Eq.symm (funext h)]; exact g
private lemma moodPack (q d w l:ℕ)(p:0<q)(r:l ≤ q)(f:w+d+1≤q)(u:ℕ)(n:Side)(g:(More n).val^4 ≤ u*(4*(12*payout d q w+l))^4):
    (↑(u*q^4):ℝ)≥ innerRate d * sites n:=by
 let ν:=4*(12*payout d q w+l); let K:ℕ:=u*(ν^4); have hp:sites n ≤ K:= by unfold sites; exact_mod_cast g
 have ht:= cost_width f r; apply (mul_le_mul_of_nonneg_left hp (innerRate_pos d).le).trans
 change innerRate d*(↑(u*ν^4):ℝ) ≤ _; push_cast; change ((4*(12*payout d q w+l):ℕ):ℝ)^4*_ ≤_ at ht -- stmt
 nlinarith only [mul_le_mul_of_nonneg_left (show (ν:ℝ)^4*innerRate d ≤ (q:ℝ)^4 from ht.trans_eq (by push_cast; rfl)) (Nat.cast_nonneg (α:=ℝ) u)] -- push_cast ν becomes sum!


open Tapestry
open CF.Pannier.Chancel.Cliplet
open Buffered.Afterglow.Tower.SlabMark
lemma wineBasket {A T:ℝ}
    (m:h ≤ P.h)(v:Inflation A P)(Z:δ≥ P.d)
    (Ft:∀ᶠ n:ℕ in atTop,∀ (N:Side),n≤N.val→Winter P.K.j δ N γ w ε ∧ ∀ M:Tulip.Male,∀ b S,Sparse d S→ HearthB R (sp b P.K.j M (1:Pane N)) S)
    (c:0 < γ)(Q:ε*R ≤ 1/3)(t': ε*(2*R+4*R*R)≤e^3)(hp:0<e)(vz:e ≤ 1)(pr:h=e⁻¹)
    (g0: 0≤a)(uz:e*(2*R+3)≤ Real.exp (-2*(a+R)))(vT:a*innerRate d ≥ T)(g: sealPrice P.V P.W - T+ blossom P.K+(A+1) ≤ -10000)(pR:0<R)
    (hq:0<q)(gq:(w+d+1) ≤ q)(vq:addgap (tent Y H)≤q) (vm:ℕ)(hv_:0<vm)(hv_₁:Mural.Invoice (tent Y H) (payout d q w) vm):
    ∀ᶠ s in atTop,∀ᶠ i in atTop, ∀ᶠ k in atTop,(Y.voyage i).kick≤k ∧ s ≤ Y.uv k ∧ (∀ b (S:Finset (Seat (Papal.count Y s i))), Sparse d S→HearthB R (sp b P.K.j (gram Y s i k).J.M (1:Pane (Papal.count Y s i))) S) ∧ ∀ (z:SU.Slot),
      let x:=grain (payout d q w); let F:=taggin Y s i k q d w x z; let ℓ:=max P.J.n (payout d q w+1)
      Cliplet.Perron P.K.j (gram Y s i k).J.M w d ℓ γ (gram Y s i k).p.threshold F ∧
      (∀ X:Fields _,‖F.frame X‖≤(1+R)^(q^4)) ∧ ∀ (f: Buffered.Family (tent Y H))(l:ℕ)(s0:ℤ)(j:Axis), exhibit Y H s i f = F.frame →
         2*Mural.gong (tent Y H)*vm*l ≤ (Papal.count Y s i).val → (Papal.count Y s i).val ≤4*Mural.gong (tent Y H)*vm*l→
         ‖sharp Y H s i k (banner j vm s0 l f)‖ ≤ Real.exp (-3000 * (l:ℝ)):=by
 subst h
 let B:=payout d q w; let ℓ:= max P.J.n (B+1); let I₀:=(4*(ℓ+ℓ+1)^4*q^4:ℕ); let κ:= (a+R)*(I₀:ℝ); have hm:0<B:= by unfold B payout; omega; -- omega due nonlinear count? +1
 obtain ⟨τ0,hτ,u⟩:= stampG_price B γ c; let x:= hat P.R.L P.x; let V(s i k):=(gram Y s i k); have hx:Tendsto (fun s:ℕ=>temp (x s)) atTop (𝓝 0):= (show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp (turnover P)
 let H':=tent Y H; let J:=addgap H'
 obtain ⟨n,hK⟩:=Ft.exists; obtain ⟨n',un⟩:= flatAcross P.K.j (P.kJ ▸ (by decide))
 filter_upwards [measured Y v (inv_pos.mpr hp |>.le) m κ, hx.eventually (ge_mem_nhds hτ),hx.eventually (ge_mem_nhds P.J.ht)] with s hZ xZ xP
 let E:= n+n'+2*(B+1)+12*B+J+4*(2*(d+1)*q)+1
 filter_upwards [hZ,(count_grows Y s).eventually_ge_atTop E] with i gV eI
 let Ns:=Papal.count Y s i; let N₁:= (More Ns).val; have hv: E ≤ Ns.val:=eI; have hi:N₁=Ns.val*2:=rfl
 obtain ⟨F₀,F₁⟩:= hK Ns (by omega)
 let W:Seat Ns→ℕ:=fun _=>0
 have hU (k):Sparkle Ns P.d (κI i s k) P.K.j := P.U.broadness _ (P.J.gran.trans ((Y.voyage i).ownership s).size) _
 let D:=(1+R)^((More Ns).val^4*(q^4))
 let G:= Real.exp (-10000*sites Ns)/D; have hg:0<D:= by unfold D; positivity
 filter_upwards [ferry_later Y s i, thaw_plot Y G (by unfold G; positivity) s] with k S φ
 let X₀:=Journey.compass Y i k s; let Y₀:= solder Y i k S.depth s
 have hn:StageTw H' Y₀ P.K.j R d (κI i s k):= ⟨tenderPack Y H s i k S, un Ns (by omega) _,F₁ _⟩ -- F₁ s b?
 let MU:= κI i s k; let th:=(gram Y s i k).p.threshold; have he: th=temp (x s):= ((congrArg BudgetPoint.threshold (prices_plot Y s i k S.enters).1).trans (Y.meter.boot s).1); have hχ(i):IsStarProjection (sp i P.K.j MU (1:Pane Ns)):=raft i ((hU k).projection 1 (guard0 P.dpos.le))
 refine ⟨S.depth,S.enters,F₁ (κI i s k),fun z=>?_⟩
 let o:=grain B
 let F:= taggin Y s i k q d w o z; let O:= wrap (More Ns) (Lifted.nodeC o); have heQ:F.broad=BlockP B O:=rfl
 let V':= VolumeX ((wrap Ns) ∘ booty o d q)
 obtain ⟨u',t,w'⟩:= feast (n:=Ns) (d:=d) (q:=q) (by omega) o w
 have hf:Cliplet.Perron P.K.j MU w d ℓ γ th F:= by
    apply repastPrize (p:= (show Sparse d V' from t)) (d:=(show Injective F.birth from u')) (g:=w') (w:=le_max_right ..); -- D want
    exact fun V=>u th (gram Y s i k).p.threshold_pos.le (he ▸ xZ) (by omega) (le_max_right ..) O V
 have hy:12*B+addgap (tent Y H) ≤ Ns.val:=by change 12*B+J ≤_; omega
 have hr:0<q^4:=pow_pos hq _
 have uB:addgap (tent Y H) ≤ B:=by
    refine vq.trans ?_
    unfold B payout
    apply (Nat.le_add_right ..).trans' (Nat.le_mul_of_pos_left _ (by omega))
 have hFee: ∀ x: Fields Ns, ‖F.frame x‖ ≤ (1+R)^(q^4):=fun i'=> hf.price (F₁ MU _ _ hf.far) (hχ _) i'
 refine ⟨hf,hFee,fun f n s0 j ht heU hU'=> ?_⟩
 obtain ⟨r,L,lT,v',len,p4,hL,YX,W,wT,hW,hΩ⟩:= Mural.cellar (F:=f) (terrain Y H (Y.ir i) s) hn uB hv_ hv_₁ j n heU hU' hy F hf rfl ht s0 -- name hv clashes prior
 let U:=exhibit Y H s i (banner j vm s0 n f)
 let Vc:= CF.Pannier.Chancel.Cliplet.probe L -- qualified alias
 have hQ(k):Sea (Fock.cutM (Tset (SN i k))) (mateK _):=by rw [←touchP]; exact tickB ..
 have hCap: Backlog Y s i k e⁻¹ T κ Vc:=by
    intro x'; exact manyYear P.J.k P.J.n lT (hU k) P.dpos.le F₀ (roofage Y i s) (he ▸ xP) (le_max_left ..) Z (fun i h b=> F₁ MU b i h) Q pR e hp vz a T (innerRate d) t' hr g0 uz vT (moodPack q d w J hq vq gq L.length Ns hL) x' _ _ (safety Y s i k x').2 (hQ s) -- tune
 have hp4: ‖X₀ Vc‖ ≤ Real.exp (-10000*sites Ns):= (gV k S.depth S.enters Vc T (lT.corsage.env) hCap).trans (Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_right g (show 0≤ sites Ns by unfold sites; positivity)))
 have Hc: ‖X₀ Vc-Y₀ Vc‖≤ Real.exp (-10000*sites Ns):=by refine (φ i S.depth Vc D lT.corsage.env (fun x=> (lT.capPrice (fun a v=> F₁ _ _ a.s (lT.granted a v).far) hχ x pR.le).trans (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ p4)))).trans_eq (div_mul_cancel₀ _ hg.ne')
 change U=_ at hΩ; change ‖Y₀ U‖^r ≤ ‖Y₀ Vc‖ at YX
 let C:=sites Ns; have ht₀:1 ≤ sites Ns:=by
    unfold sites; exact one_le_pow₀ (by exact_mod_cast ((More Ns).property : 1≤ (More Ns).val))
 have hu:(L.length:ℝ) ≤ sites Ns:=by unfold sites; exact_mod_cast p4
 have hu₀:r ≥ 1:=v'
 have hr₀: (r:ℝ) ≥ 1 := by exact_mod_cast hu₀
 have hxK:0 ≤ (n:ℝ):= Nat.cast_nonneg _
 have hrA: 4* (n:ℝ)*r ≤ sites Ns:=by rw [len] at hu; push_cast at hu; exact hu
 have hs:(n:ℝ)>0:=by
    have hh:0<(Papal.count Y s i).val:=(Papal.count Y s i).property
    have hg:0<n:= by by_contra! h; rw [show n=0 from by omega,mul_zero] at hU'; omega
    exact_mod_cast hg
 have hsΩ: (n:ℝ) ≥1:=by exact_mod_cast ((Nat.cast_pos.mp hs) : n ≥ 1)
 have hHt: Real.exp (-10000*C)+Real.exp (-10000*C) ≤ Real.exp (-9999*C) := calc
     _ ≤ Real.exp C * Real.exp (-10000*C):= by
        have h:2 ≤ Real.exp C:= by unfold C; linarith only [Real.add_one_le_exp (sites Ns),ht₀]
        nlinarith [Real.exp_pos (-10000*C)]
     _ = _:= by rw [← Real.exp_add]; ring_nf
 have hΩK: ‖Y₀ U‖ ≤ Real.exp (-3100*(n:ℝ)):=by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le v'.ne').mp
    refine YX.trans (((norm_le_norm_sub_add (Y₀ Vc) (X₀ Vc)).trans (add_le_add ((norm_sub_rev ..).trans_le Hc) hp4)).trans (hHt.trans ?_))
    rw [←Real.exp_nat_mul,Real.exp_le_exp]; unfold C; nlinarith
 have hzW: Backlog Y s i k e⁻¹ T κ Vc:=hCap -- optional
 have HΩ: ‖X₀ U-Y₀ U‖≤ Real.exp (-10000*sites Ns):=by
    rw [hΩ]
    refine (φ i S.depth (CF.Pannier.Chancel.Cliplet.probe W) D wT.corsage.env (fun x=> (wT.capPrice (fun a v=> F₁ _ _ a.s (wT.granted a v).far) hχ x pR.le).trans (pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ (le_trans (show W.length≤ L.length from by rw [len,hW]; exact Nat.le_mul_of_pos_right _ v') p4))))).trans_eq (div_mul_cancel₀ _ hg.ne')
 rw [actualRead]
 change ‖X₀ U‖ ≤ _
 apply ((norm_le_norm_sub_add _ (Y₀ U)).trans (add_le_add HΩ hΩK)).trans
 calc _ ≤ Real.exp (-3100*(n:ℝ))+Real.exp (-3100*(n:ℝ)):= by exact add_le_add (Real.exp_le_exp_of_le (by nlinarith)) le_rfl
      _ ≤ Real.exp (100*(n:ℝ))*Real.exp (-3100*(n:ℝ)):= by
          have ht :2 ≤ Real.exp (100*(n:ℝ)) :=by linarith only [Real.add_one_le_exp (100*(n:ℝ)),hsΩ]
          nlinarith [Real.exp_pos (-3100*(n:ℝ))]
      _ = _:= by rw [←Real.exp_add]; ring_nf
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.wineBasket
