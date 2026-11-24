import YM.SU5.Twilight.Majesty
set_option autoImplicit false
set_option maxHeartbeats 164000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {h x delay : ℝ} {C D R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
open Pitching Focus AnalyticBridge.Annulus1AD
namespace Branch
section
variable {P} {A:Branch W m k x N0} {Z:Haro.ΘS 1}
-- Second height: Vp929's actual stronger Shop at other size gate. No new beta sequence.
variable {P':Prescription R B} {D' R0' C':ℝ→ℝ}{N0':ℕ} {w y u y₀:ℝ} {p p':BudgetPoint}{l n:Side}{β:ℝ}
variable (cut:CutFrom R0 D C J q h P N0 delay) (C0:CutFrom R0' D' C' J q w P' N0' u) (H:Service V U W J q w D' C' R0' P' N0' u)
include cut C0 H
lemma alt_out {Q:Location (R:=R) B l n}(pS:Location.Request V U W J q Q N0 y p p') (q':Location.Request V U W J q Q N0' y p p') (ly:delay≤ y)(qy:u ≤ y) {G F:Corr (mid n B)} (pβ: enters (y+billX R.L) (β:ℂ))(G₀: Charged p' Q.input K.j R.L.val h (3*dleaf R.L y) G)(F₀:Charged p' Q.input K.j R.L.val w (3*dleaf R.L y) F){a c:ℂ}(g:denZ (Q.buildIn V p' β G a) U Q.fine =ᵐ[city _] denZ (Q.buildIn V p' β F c) U Q.fine): let T:=P _ _ Q y p p'; let L':=P' _ _ Q y p p'; let Y₀:=T.output V Q p β G a; let Y':=L'.output V Q p β F c
 Y₀.beta=Y'.beta ∧ T.wave β G=L'.wave β F ∧ Charged p Q.output K.j R.L.val w (dleaf R.L y/1000) (L'.realArr β F) ∧ ∀ z, Rue.FleetS p.threshold z.1 → denZ Y₀ U Q.coarse z=denZ Y' U Q.coarse z:=by
 obtain ⟨K₀,r,t,hy,hZ,Z⟩:= cut.ships _ _ _ _ _ _ ly pS; obtain ⟨_,r₀,g₀,zV,f,Y⟩:= C0.ships _ _ _ _ _ _ qy q'; letI:= hZ; letI:= f; obtain ⟨Z,hX,Vq⟩:= Z; obtain ⟨Y,aP,aY⟩:= Y
 let d':= 3*dleaf R.L y; have ht: 0≤ d':= mul_nonneg (by norm_num) K₀.high.le
 have hp: Both (Charged p' Q.input K.j R.L.val w d') (F,0):= ⟨F₀,Charged.zero.mono ht⟩
 have he: Both (Charged p' Q.input K.j R.L.val h d') (G,0):= ⟨G₀,Charged.zero.mono ht⟩
 have H':= ((H.provides _ _ _ _ _ _ qy q').cost _ _ pβ hp).1.1
 obtain ⟨z,h₁,h₂⟩:= Z.prosper Y (submits K₀ pβ he) (submits K₀ pβ hp) g pS q'; rw [Vq,aY]; rw [aY] at H'
 exact ⟨h₁,z,H',fun x y=> h₂ x y y⟩
-- grammar for *coherent alternate trajectory* with SAME gravitational beta; actual cutoff retained.
omit cut C0 H
variable (w P P') (A:Branch W m k x N0) (b:Bet k)
local notation "κ" i:max => A.T.a i
local notation "ℶ" => hat R.L x
abbrev Voucher (i:ℕ) := let R₀:=A.gram P b i; let R₁:=A.gram P' b i
 ChargedAt w A i (A.chargeLevel P' b i) (dleaf R.L (hat R.L x i)/1000) ∧
 ∀ z, Rue.FleetS (A.T.a i).threshold z.1→ denZ R₀ U (A.loom i) z=denZ R₁ U (A.loom i) z
-- real/corr complex: used `arrays` not realPart separately! real Bet g assures input comlex `A.chargeLevel` also. Need Haro uniqueness + real
abbrev Alternate (i:ℕ) := Voucher P P' w A b i ∧ (A.corr P' b i).2=0 ∧ ∀ _ : i<k,(A.active P' b i).beta=(b.read i).re ∧ A.wave P b i=A.wave P' b i
-- CHECK argument order P setup
#check @Voucher
#check @Alternate
variable {w P P' b A} {α:ℝ}
variable (α0: Bon J q h D delay A)(S: Service V U W J q h D C R0 P N0 delay)(s:Solved P A α b) (capital:A.start=0)
include cut C0 H α0 S s capital
lemma redeem {i:ℕ}(v:i≤k)(pv:u ≤ ℶ i)(a:∀ l:ℕ,i≤l→ l<k → N0'*radiusB (ℶ l) ≤ (Domain (mesh m R.L l) B).val) : A.Alternate P P' w b i:=by
 rcases v.eq_or_lt with e|e
 · subst i; have hz (Q:Prescription R B):A.corr Q b k=0:=by rw [corr_top,capital]; rfl
   refine ⟨⟨?_,?_⟩,by rw [hz]; rfl,fun v=> (lt_irrefl _ v).elim⟩
   · unfold chargeLevel; rw [hz]; apply (by exact Charged.zero: ChargedAt w A k (0:Pair (Corr (cell m B R.L k))).1 0).mono; exact div_nonneg (α0.clocks k).leaf.le (by norm_num)
   intro z g; rw [gram,gram,chargeLevel,hz,chargeLevel,hz,offset.eq_1 P A b k, offset.eq_1 P' A b k,dif_neg (lt_irrefl _), dif_neg (lt_irrefl _)]
 let c:= i+1; have h₀:ℶ i ≤ ℶ c:= hat_mono (by omega); obtain ⟨⟨hf,hq⟩,g,Lq⟩:= redeem e -- tune
      (pv.trans h₀) (fun j t=> a j (t.trans' (Nat.le_succ i)))
 let S₁:=A.gram P b c; let S':=A.gram P' b c; let Q:= A.toSpine.address i; let R₁:=A.gram P b i; let R':=A.gram P' b i; let F':=A.corr P' b c; let t:=(b.read c).re; let Z:= (A.active P b i); let θ':= A.active P' b i
 have hx:=α0.request i e; have he: Location.Request V U W J q Q N0' (ℶ i) (κ i) (κ (i+1)):= { hx with size:=a i le_rfl e }
 have hp: enters (ℶ i+billX R.L) (t:ℂ):= hat_step i ▸ (α0.beta_ok S s.toRealQ c e).2
 have hQ:= α0.flow (α0.charged S s.toRealQ (i+1) e); have hy' := (α0.clocks i).leaf_mono (ℶ c) h₀; have hy:= (α0.clocks i).leaf
 have hV: ChargedAt w A c (A.chargeLevel P' b (i+1)) (3*dleaf R.L (ℶ i)):= hf.mono (by linarith only [hy',hy])
 have hv:denZ (Q.buildIn V (κ c) t (S₁.F,S₁.K) S₁.v) U Q.fine =ᵐ[city _] denZ (Q.buildIn V (κ c) t (S'.F,S'.K) S'.v) U Q.fine :=by
    rw [show Q.buildIn V (κ c) t (S₁.F,S₁.K) S₁.v=A.gram P b (i+1) from (gram_fine P A b i e).symm,show Q.buildIn V (κ c) t (S'.F,S'.K) S'.v=A.gram P' b (i+1) from (gram_fine P' A b i e).symm]
    exact (ae_fleet he.isle').mono fun i α0=> hq i α0
 obtain ⟨(hζ: Z.beta=θ'.beta),h₁,h₂,h₃⟩:=alt_out cut C0 H hx he (α0.late.trans (Vale.crown ..)) pv hp hQ hV hv
 let F:=A.op P' i; have ht:= (H.provides _ _ _ _ _ _ pv he).real t _ S'.v hp hV; have ht':A.corr P' b i=F.arrays t (A.chargeLevel P' b (i+1),0):=by
    rw [A.corr_step P' _ i e]; nth_rw 1 [show A.corr P' b (i+1)=(A.chargeLevel P' b (i+1),0) from Prod.ext rfl g]; rw [show (t:ℂ)=b.read (i+1) from s.toRealQ.coeRe _ e]
 have hα:F.realArr t (A.chargeLevel P' b (i+1))=A.chargeLevel P' b i:= congrArg Prod.fst ht'.symm
 have hψ: Z=A.gram P b i:= α0.success S s.toRealQ _ e (α0.paysStep S s i e)
 have hz':θ'.beta=(b.read i).re:= hζ.symm.trans (α0.paysStep S s i e)
 have hΓ: θ'= A.gram P' b i:=by
    change construct (κ i) (V.L.path (k-1-i+1)) K.top.clip _ θ'.beta (F.realArr _ _) (F.offset _ _ _)=_
    rw [show k-1-i+1=k-i by omega,hz']; rw [hα]; rw [gram, offset.eq_1 P' A b i, dif_pos e]; rfl
 refine ⟨⟨?_,fun z x=> Eq.trans (congrArg (fun b'=>denZ b' U _ z) hψ.symm) ((h₃ z x).trans (congrArg (fun b'=>denZ b' U _ z) hΓ))⟩,?_,fun _=>⟨hz', h₁⟩⟩
 · rw [←hα]; exact h₂
 exact (congrArg Prod.snd ht').trans ht.1
termination_by k-i
omit cut C0 H α0 S s capital
/-- Same inflation rate as for Stow. -/
private lemma grows_spread (d:Grace K R L) (x:ℝ)(t:ℕ): ∀ᶠ s in atTop, t*(radiusB (hat R.L x s))^3 ≤ R.L.val^s:=by
 let a:= billX R.L; let b(s:ℕ):= R.L.val ^ s
 let V(s):= hat R.L x s; let h:= stage_slope d x
 -- compare r^3 ≤ V at even huge s. pay arbitrary linear ≤ b
 have hz: Tendsto (fun i:ℕ=> (radiusB (V i):ℝ)^3/(V i)) atTop (𝓝 0):=by simpa only [Real.rpow_one,Function.comp_def,V] using (Work.E09.radiusB_small 1 zero_lt_one 3 |>.tendsto_div_nhds_zero).comp h
 have hf:1 < (R.L.val:ℝ):= by exact_mod_cast (show 1 < R.L.val by have t:=d.tallX; omega)
 have ht := tendsto_pow_const_div_const_pow_of_one_lt 1 hf
 have hp':Tendsto (fun i:ℕ=> (t:ℝ)* V i / (R.L.val:ℝ)^i) atTop (𝓝 0):=by
    have hh := ht.const_mul a; have hl:= tendsto_const_nhds.div_atTop (f:=fun i:ℕ=> x) (tendsto_pow_atTop_atTop_of_one_lt hf); let H := (hl.add hh).const_mul (t:ℝ); have he: Tendsto (fun i:ℕ => (t:ℝ)*(x/(R.L.val:ℝ)^i + a*((i:ℝ)/(R.L.val:ℝ)^i))) atTop (𝓝 0):=by simpa only [pow_one,mul_zero,add_zero] using H
    refine he.congr ?_; intro i; unfold V hat a; ring
 filter_upwards [h.eventually_gt_atTop (0:ℝ),hz.eventually (ge_mem_nhds zero_lt_one),hp'.eventually (ge_mem_nhds zero_lt_one)] with s w v f
 exact_mod_cast (mul_le_mul_of_nonneg_left (show (radiusB (V s):ℝ)^3 ≤ V s from ((div_le_one w).mp v)) (Nat.cast_nonneg (α:=ℝ) t)).trans ((div_le_one (by positivity)).mp f)
include cut C0 H S
/-- Arbitrarily long *interval* of heights for same h', all periods. Tail in s, not depending i,k. -/
lemma redeem_time : ∀ᶠ i in atTop, ∀ (m' :Side) (k:ℕ)(A:Branch W m' k x N0)(b:Bet k) (p:Bon J q h D delay A), Solved P A α b → A.start=0 → i ≤ k → A.Alternate P P' w b i:=by
 have he:∀ᶠ i:ℕ in atTop,∀ j≥i, N0'* (radiusB (hat R.L x j))^3 ≤ R.L.val^j:=by
   obtain ⟨k,h⟩:= eventually_atTop.1 (grows_spread V x N0'); exact (eventually_ge_atTop k).mono (fun i v j t=>h j (v.trans t))
 filter_upwards [he,(stage_slope V x).eventually_ge_atTop u] with i hz h₀ m t A b p S0 V0 hk
 refine redeem cut C0 H p S S0 V0 hk h₀ fun l v p=> ?_
 let B':=radiusB (hat R.L x l); have h:N0'* B'^3≤R.L.val^l:=hz l v
 have hh: (A.T.a l).B = B':=(A.T.boot l).2.1; have ht:1 ≤ B':= hh ▸ (A.T.a l).B_pos
 apply le_trans (Nat.mul_le_mul_left N0' (show B' ≤ B'^3 by simpa only [pow_one] using (Nat.pow_le_pow_right ht (show 1 ≤ 3 by omega))))
 apply le_trans h; let n:= (mesh m R.L l).val; have ht:R.L.val^l ≤ n:= Nat.le_mul_of_pos_left _ m.property
 exact ht.trans ( ((Nat.le_mul_of_pos_right n Nat.zero_lt_two|>.trans (Nat.le_mul_of_pos_right _ B.property))|>.trans (Nat.le_mul_of_pos_right _ Nat.zero_lt_two)))
omit cut C0 H
include α0 s
lemma redeem_v {i:ℕ}(e:i≤k)(uA:A.Alternate P P' w b i)(hh:0≤h)(hz:0≤w): |(A.gram P b i).v.re-(A.gram P' b i).v.re| ≤ (2*(dleaf R.L (hat R.L x i)/1000))*sites (cell m B R.L i):=by
 have ht:= α0.can.cape i; have hV:= J.gran.trans ht.size; have hS(z:Orbit (cell m B R.L i)):= (ht.paid.paid z).shrink J.hr.le
 rw [two_mul]; exact compare_real U _ _ hV hS hh hz (α0.charged S s.toRealQ i e).toCost (uA.1.1).toCost (fun x y z=> uA.1.2 x y)
end
end Branch
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.Branch.alt_out
#print axioms YM.CF.Py.Rate.Branch.redeem
#print axioms YM.CF.Py.Rate.Branch.redeem_time
#print axioms YM.CF.Py.Rate.Branch.redeem_v
