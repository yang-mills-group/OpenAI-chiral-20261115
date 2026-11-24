import GaugeFieldConstruction.Rinket
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 70000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Work.F03
open Housing ModuleB Flot
namespace HushP
open Haro Moto Pastry Bank
variable (o:Skye.Seat n) (L:leadF Gem Gem)(J:leadF Gem Sut)(p:BudgetPoint)
abbrev CoverP := terrace o p (bloomT L J)
abbrev flowF :InkD n:= fun i=> hollow (CoverP o L J p i)
lemma κFish (p₀: p.power≤3)(h:p.order≤6)(u:L.flip=L)(w: 10 < (More n).val) : fave p o (flowF o L J p)=L∧ claw p o (flowF o L J p)=J:=by
 let T:= bloomT L J; let W:= flowF o L J p; let z:=spike SU.group
 have hx :term W= terrace o p T ∘ increment 1:=funext fun i=> hullB _; have hz:‖z‖=1:= spike_norm Thera.yet_one
 have ha(i:Gem)(q:GateI):= π_sun (o:=o) w i z p q; have hv(i:Sut)(q:GateI):=π_shadow (o:=o) w i z p q
 have he:=bloom_r L u J
 constructor <;> apply ContinuousLinearMap.ext <;> intro i <;> apply ContinuousLinearMap.ext <;> intro j
 · change ploy W (gateC o p.threshold (hem i z)) (gateC o p.threshold (hem j z))= _; rw [ploy_iter,hx, show iteratedFDeriv ℝ 2 _ _ _=T (i,0) (j,0) from ψPlane _ _ z hz T _ _ he (fun x=> ac_pack i x ▸ ha _ _) (fun x=> ac_pack j x ▸ ha _ _) p₀ h]; rw [show T _ _=_ from bloom_apply L J (i,0) (j,0),map_zero,map_zero,add_zero, add_zero]
 change ploy W (gateC o p.threshold (hem i z)) (gateT o p.threshold (loomH j z))= _; rw [ploy_iter,hx, show iteratedFDeriv ℝ 2 _ _ _=T (i,0) (0,j) from ψPlane _ _ z hz T _ _ he (fun x=> ac_pack i x ▸ ha _ _) (fun x=> ve_pack j x ▸ hv _ _) p₀ h]; change L i 0+(J i j+J 0 (0:Sut))=_; rw [map_zero,map_zero (J 0), add_zero,zero_add]
lemma keel_Z (A:Pane n): orbitPH (flowF o L J p A)=0:=Moto.hol_l _
lemma knit (M:Tulip.Male) (h:ℝ) : let Q:= flowF o L J p; winJ o M h (orbitPH (Q 1))= (show Ole Views Tap.Pal from (0,0,0))∧ landA M o Q p h=0∧ lifeH Q 1=0:=by
 intro Q; have he(x):orbitPH (Q x)=0:=keel_Z ..; let i:=(0:Op (Single n)); have hz:streamF o i h =0:=by funext u; simp [i,streamF,hill_Z]
 have hx:TabX o M h i=0:=by funext x; unfold TabX; rw [hz]; simp
 rw [he 1]; refine ⟨((tab M i).equal (Eventually.of_forall fun i=>congrFun hx i)).unique (AptK.const _), ?_,(hullB ..).trans (ψ_flat ..)⟩
 apply ContinuousLinearMap.ext; intro x; let v:=gateC o p.threshold x; have hR: Paint Q v=0:=by
    ext a b; unfold Paint; rw [Matrix.of_apply, show portE Q a b=fun _=>0 from funext (fun i=> by unfold portE; rw [he]; rfl)]; simp
 change sectorJ (Paint Q v) _ _ _=0; rw [hR,seat_b]; change _*streamF o i h 0 *_=_; rw [hz]; simp
lemma Ψ_spurs(a:ℝ)(q:0≤a)(o':Skye.Seat n)(Z:leadF rowS rowS)(s:Tickets)(k:p.order≤6)(x:ℂ)(c' d:ℝ)(h:Haw p o' (Pax o') (πon o' s.1 p) a)(g:Haw p o' (Pax o') (πon o' s.2 p) a) (w:tautF (monover x) ≤ c')(e:0≤ c'): Haw p o' (Pax o') (ψTile o' p s x) ((2:ℝ)^6*c'*a*a):=by
 apply gum (witch (monover _) h g); apply mul_le_mul_of_nonneg_right _ q; apply mul_le_mul_of_nonneg_right _ q; change 2^_ * tautF (monover x) ≤ _; apply mul_le_mul (pow_le_pow_right₀ (by norm_num) k) w (taut_nonneg _) (by positivity)
-- bound amplitudes v fixed dimension via norm. 
omit o p L J
lemma allotB (x:ℂ): tautF (monover x) ≤ ‖x‖*tautF (monover 1):=by
 let E:=monover 1; let V:=monover x
 have hf(i j:SU.group.Color): ‖V i j‖ ≤ ‖x‖*(tautF E* ‖i‖ * ‖j‖):=by
    rw [show V i j=x*(E i j) from (by unfold E V; rw [mono_apply,mono_apply,one_mul]),norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); exact ((E i).le_opNorm j).trans (mul_le_mul_of_nonneg_right (E.le_opNorm i) (norm_nonneg _))
 have hp: 0≤ ‖x‖*tautF E:=mul_nonneg (norm_nonneg x) (taut_nonneg _)
 apply ContinuousLinearMap.opNorm_le_bound V hp; intro i; apply ContinuousLinearMap.opNorm_le_bound (V i) (M:=‖x‖*tautF E *‖i‖) (mul_nonneg hp (norm_nonneg _)); intro j; exact (hf i j).trans_eq (by ring)
lemma tollB (k:Tickets):∃ C:ℝ,1≤C∧ ∀ (L:leadF Gem Gem)(J:leadF Gem Sut),‖(1/2:ℂ)*bloomT L J (ζedge k.1) (ζedge k.2)‖≤ C*(‖L‖+‖J‖):=by
 let i:= ζedge k.1; let j:= ζedge k.2; let i0:=‖i.1‖; let i1:=‖i.2‖; let j0:=‖j.1‖; let j1:=‖j.2‖; let c:= ‖(1/2:ℂ)‖; let H:= max 1 (c*(i0*j0+i0*j1+j0*i1)); refine ⟨H,le_max_left ..,fun L J=>?_⟩
 have hL:‖L i.1 j.1‖≤ ‖L‖*i0*j0:=(L i.1|>.le_opNorm j.1).trans (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)); have hJ(x y): ‖J x y‖≤ ‖J‖*‖x‖*‖y‖:=(J x|>.le_opNorm _).trans (mul_le_mul_of_nonneg_right (J.le_opNorm x) (norm_nonneg _))
 rw [norm_mul]; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_right ..) (add_nonneg (norm_nonneg L) (norm_nonneg J)))
 have hb:= add_le_add hL (add_le_add (hJ i.1 j.2) (hJ j.1 i.2))
 change c * ‖_‖ ≤ _; rw [bloom_apply]; apply (mul_le_mul_of_nonneg_left ((norm_add_le ..).trans ((add_le_add (le_refl _) (norm_add_le ..)).trans hb)) (norm_nonneg _)).trans
 let X:= ‖L‖; let Y:=‖J‖
 change c*(X*i0*j0+(Y*i0*j1+Y*j0*i1))≤c*(i0*j0+i0*j1+j0*i1)*(X+Y)
 have hc:0≤ c:=norm_nonneg _; have hx:0≤X:=norm_nonneg L; have hy:0≤ Y:=norm_nonneg J; have hi:0 ≤ i0:=norm_nonneg i.1; have hv:0 ≤ i1:=norm_nonneg i.2; have he:0 ≤ j0:=norm_nonneg j.1; have hh:0≤ j1:=norm_nonneg j.2
 linarith only [mul_nonneg (mul_nonneg (mul_nonneg hc hx) hi) hh,mul_nonneg (mul_nonneg (mul_nonneg hc hx) he) hv,mul_nonneg (mul_nonneg (mul_nonneg hc hy) he) hi]
lemma glyphs : ∃ C:ℝ,1≤C∧∀ (n:Side)(o:Skye.Seat n)(L:leadF Gem Gem)(J:leadF Gem Sut)(p:BudgetPoint),p.power≤3 → p.order≤6 → Haw p o (Pax o) (CoverP o L J p) (C*(‖L‖+‖J‖)):=by
 choose f hf v using tollB; let u:=tautF (monover 1); have hh:0≤u:=taut_nonneg _; obtain ⟨A,h,p⟩:= F_grade; let K(i):=(2:ℝ)^6 * (f i * u)* A*A; let d:= max 1 (∑ i:Tickets,K i);
 refine ⟨d,le_max_left ..,fun n o L J p' pP pQ=>?_⟩; let qx:= ‖L‖+‖J‖; apply gum (Housing.pets (n:=n) (p:=p') (Y:=fun i=> ψTile o p' i (νt o p' (bloomT L J) i.1 i.2)) (univ:Finset Tickets) (C:=fun i=> K i*qx) (fun i _=>?_))
 · rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (add_nonneg (norm_nonneg L) (norm_nonneg J))
 let F:=bloomT L J; let x:=νt o p' F i.1 i.2; have ht:tautF (monover x) ≤ f i*qx*u:=(allotB _).trans (mul_le_mul_of_nonneg_right (v i L J) hh); apply gum (Ψ_spurs p' A (zero_le_one.trans h) o F i pQ x (f i*qx*u) 0 (p _ _ _ _ pP pQ) (p _ _ _ _ pP pQ) ht ((taut_nonneg _).trans ht)); unfold K; exact le_of_eq (by ring)

end HushP
end Lenten
end YM.CF.TableF
end
