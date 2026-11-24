import GaugeFieldConstruction.Pelerine3
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 260000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Iona Isle Rio Py Nor Py.Riant
variable (P:BudgetPoint)(σ:I→Seat n)
lemma Tin_K (b:List I)(v:Key I):True:=True.intro -- remove
private lemma τRain (Z:Phys n→L[ℂ] Phys n)(k:I)(F G:Key I→ Phys n)(v:Kin σ F G): Kin σ (fun z=> F z+z k • Z (F z)) (fun z=> G z+z k • Z (G z)):= by
 apply loft_add v; let A:= ContinuousLinearMap.lsmul ℂ ℂ (E:=Phys n)
 exact (Kin.refl σ (north_r k)).prod A (Kin.map v Z)
lemma Prefixe (k:I)(P':FC (Single n))(F G:Key I→ Phys n)(v:Kin σ F G): Kin σ (fun z=> acts (1+z k • P') (F z)) (fun z=> acts (1+z k • P') (G z)):=by
 have hp(Z:Key I→ Phys n)(x:Key I):acts (1+x k • P') (Z x)=Z x+x k • (acts P') (Z x):=by rw [act_add,act_one, show (acts (x k • P')) _=_ from act_smul (x k) P' (Z x)]
 simp_rw [hp]; exact τRain σ (acts P') k F G v -- acts? CLM
section
variable {m B L:Side}{e :ℝ}{j:ℕ}{hd:Odd L.val}{Y':Pricing j L hd (Thread j)}(U:Grasp Y' B e) (T₀:Loom (mid m B))(H:GramM (mid m B))
local notation "Nν"=> mid m B
variable (σ:I→Seat (mid m B))
variable (F: KK I (Copy (mid m B)) (mid m B)) (W0: Finset I→Vow.Pax (mid m B))(Q0: Finset I→ Vow.Cusp (mid m B))(A:XE I (InkD (mid m B)) (mid m B))
variable (Q: LeaseQ γ (mid m B)) (R K:ℕ){J:Type}[Fintype J](C:I→J→Factor3 (mid m B))(r h a ℓ Ω η:ℝ)(k:ℕ)
variable (S:Ids (mid m B))
local notation "P0"=>H.p
variable (T : KI I (mid m B)→ℝ)(V Y:WA3 I (mid m B)→ℝ) (fV:BillF H.p σ h r K T F)(p: Plen_E H.p σ W0 Q0 h r V Y)(uV:0≤ V)(uY:0≤Y)(hr:0<r)(h₀:1≤h)
local notation "νB"=>H.p.B
local notation "HN"=>ΦNow σ F
variable (Vx:γ→ℝ)(V0:I→J→ℝ)(s:Finset I)(p0:Momentum3 H.p σ Q R K C r h a ℓ Vx V0 s)
local notation "Γ0"=> penStep H.p σ F W0 Q0 Q R C S
abbrev MoveL (l:List I):=Book3 H.p σ F W0 Q0 Q R C S l
local notation "P₁"=> Key I → RegBudget Nν
local notation "K₁"=> Key I → ForceBudget Nν
variable (c:Orbit (mid m B)→ Key I→ℂ)(p':∀ x:Orbit (mid m B),Rue.FleetS H.p.threshold x.1→∀ z:Key I,exponentL H.p (H.F+Canz σ _ A z) x.1= c x z • (1:Cipher (mid m B))+(coldE H.p (WritV σ W0 z) x - fuelV H.p (WritV σ Q0 z) x))
variable (z0:ℝ)(mZ:η=Eta4 k H.p.B)(q:0≤Ω)(hq:Boot4 H.p.B Ω η ℓ z0 (Flow4 k H.p.B)) (L0 M:List I)(v:L0.toFinset⊆s)(sU:supplyL k σ (L0++M))(z₁:0≤a)(ht:∀ i:Seat (mid m B),postG pastMask (V+Y) (March H.p.B (a+7*ζd)) i + pointX cloudK T (March H.p.B (a+7*ζd)) i ≤ z0)
variable (W:Orbit (mid m B))(hp: FleetS H.p.threshold W.1)(u:H.slip=0)
variable (x:IsStarProjection (Dial.spar j H.J.M (T₀ W)))
variable (hw: ∑ i:γ, Q.raw i W=Hest.boat (H.J.P.den (T₀ W))) (Pz:I→ FC (Single (mid m B)))
variable (Y0:∀ i∈s,∀ u:Wave (Dwell (mid m B)), let L:= Sault.ballL (nursery (Dial.spar j H.J.M (T₀ W)) x) (changeM U (T₀ W) H.J.M); L (acts (∑ j:J,(C i j).raw W) u)= acts (Pz i) (L u))
abbrev WarmGram (X:Rio I (mid m B))(z:Key I):= ΜΓ H (JFood A X H.F σ z) (ΦNow σ F X z)
local notation "ΓΦ" => MoveL H σ F W0 Q0 Q R C S
local notation "Aχ" X:max z:max=> WarmGram H σ F A X z
include p sU p0 q hp hq u uV uY hr z₁ -- tune
include fV ht v h₀ mZ Y0 hw p'
def LaterOp (D:I→FC (Single n))(L:List I)(z:Key I):FC (Single n):=Roots.brewK D L.reverse z
lemma Carry_p: Kin σ (fun z=>denZ (Aχ (ΓΦ L0) z) U T₀ W) (fun z=>acts (LaterOp Pz L0 z) (denZ (WarmGram H σ F A 0 z) U T₀ W)):=by
    induction L0 using List.reverseRecOn generalizing M with
    | nil=>
       simp only [LaterOp,List.reverse_nil,Roots.brewK,List.map_nil,List.prod_nil,act_one] -- tune base. need Kin.refl.
       apply Kin.refl σ
       -- River via board formula.Mod.Integr
       let X':=FortX3 F 0
       let E:=JFood A (0:Rio I Nν) H.F σ; let D:=ΦNow σ F 0
       obtain ⟨p,q,w⟩:= QcFarm P0 σ F W0 Q0 H.F A 0 h r hr K T fV 0 Weighted.free c p'
       let V(z:Key I):= CtTurn T₀ H W (E z) (D z)
       let Z:=fun z=> denZ (WarmGram H σ F A 0 z) U T₀ W
       let Λ:= LinearMap.toContinuousLinearMap (ballL (nursery _ x) (changeM U (T₀ W) H.J.M)); let Lz := Complex.exp (H.betaL T₀ W)
       let B:= fun z:Key I=> acts (V z).val (vacuum _)
       let ε(z:Key I):=ΓTurn U T₀ H W x u (E z) (D z)
       have hZ(z):Z z= Lz • Λ (B z):= ε z
       have hE: River V:=by
          let Qz(z:Key I)(i:KI I Nν):=Tuner.Mu_z X' z i W
          have hg(i):River (fun z:Key I=>Qz z i):= arc0 ..
          let Q0(z:Key I):= fueled H.p (D z) W; let Ω:= flags H.p.threshold W.1
          have he(z:Key I): Q0 z=hum Ω X'.z (Qz z):=by rw[←Hum_split,show PourUp X'.z (Qz z)= _ from w W hp z, ←hum_pay hp]
          have hp(y:Finset (KI I Nν)):River (fun z:Key I=>∏ i∈y,Qz z i):=by
             induction y using Finset.induction_on with|empty=> simp_rw [prod_empty]; exact zeroR _| insert i y q ih=> simp_rw[prod_insert q]; exact (hg i).mul_T ih
          apply River.mul_T (River.exp_V (dub_V (zeroR (Hest.boat _)) (p W ‹FleetS _ _›))) (show River Q0 from ?_)
          rw [funext he]; exact (tip_bank _ _ (fun i _=>hp i)).1
       have hB:River B:=by
          let C:=Span_D3 (0:Cipher Nν)
          have ht:C ∘ V=B:=funext (fun z=>by change acts ((exp 0*(V z)):Cipher Nν).val (vacuum _)=_; rw [exp_zero, one_mul])
          rw[←ht]; exact sc_V hE C
       change River Z; rw [funext hZ]; exact River.scale (sc_V hB Λ) Lz
    | append_singleton l i ih=>
       have uP: i∈s:=v (by simp); have Pp:l.toFinset⊆ s:=fun i t=>v (List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp t)))
       have tR:supplyL k σ (l++(i::M)):=by rw[List.append_assoc] at sU; exact sU
       have ht':= ih (i::M) Pp tR
       obtain ⟨V',hV,b⟩:=ReceiptT H.p σ F W0 Q0 Q R K C r h a ℓ Ω η k S T V Y fV p uV uY hr h₀ Vx V0 s p0 z0 mZ q hq l (i::M) Pp tR z₁ ht
       let Φ:=ΓΦ l
       let E:=JFood A Φ H.F σ; let E':=ΦNow σ F Φ
       let X:=Frame3 σ W0 Q0 Φ; let Vξ:=FortX3 F Φ; let B':= Platform Q (C i) P0 R
       obtain ⟨A',U'⟩:= Libero P0 σ F W0 Q0 Φ h r hr V Y K T fV V' hV p uV uY
       obtain ⟨hT,hz⟩:= Maxim3 P0 σ F W0 Q0 Φ h r hr V Y K T fV V' hV p uV uY
       obtain ⟨k0,k₁,K₂⟩:= QcFarm P0 σ F W0 Q0 H.F A Φ h r hr K T fV V' hV c p'
       obtain ⟨c₁,v₁⟩:= k₁ W hp
       let Z:= Γ0 Φ i
       have hP:= bookTurn X Q i Vξ (C i) B' S σ P0 A' (p0.act _ uP) p0.leased (fun i=> padd_on _ _ _ _) U' (p0.aligns _ uP) h₀ hr hz hT p0.ge (p0.pos _ uP) E E' W hp (k0 W hp) (K₂ W hp) _ hw c₁ v₁ -- tune order
       have v(z:Key I):ΓΦ (l++[i])=Φ+Z:=Book3_cons ..
       have e(z:Key I): Aχ (ΓΦ (l++[i])) z= ΜΓ H (E z+Canz σ _ (pureX Z) z) (E' z+Canz σ _ Z.B z):=by
          rw[v z]; unfold WarmGram JFood E E' ΦNow; congr 1
          · funext j; change H.F j+_= _; rw [show RX A (Φ+Z)= RX A Φ+pureX Z from (by change A+(Φ.X+Z.X+(Φ.Y+Z.Y))= A+(Φ.X+Φ.Y)+ (Z.X+Z.Y); abel),puff_add]; change H.F j+(_+_)= _; rw [←add_assoc]; rfl
          funext j; rw[show BX F (Φ+Z)= BX F Φ+Z.B from (by change F+(Φ.B+Z.B)= _; rw[←add_assoc]), puff_add]; rfl
       let Zx(z):= denZ (WarmGram H σ F A 0 z) U T₀ W
       have pL(z:Key I): LaterOp Pz (l++[i]) z=(1+z i • Pz i)*LaterOp Pz l z:=by rw [LaterOp,List.reverse_append,List.reverse_singleton]; rfl
       simp_rw [pL,e]
       apply Kin.trans (comeB U T₀ H W x u σ (Pz i) i (∑ j:J,(C i j).raw W) (Y0 i uP) E (fun z=> E z+Canz σ _ (pureX Z) z) E' (fun z=> E' z+Canz σ _ Z.B z) hP)
       have h(z:Key I): acts ((1+z i • Pz i)*_) (Zx z)=acts (1+z i • Pz i) (acts (LaterOp Pz l z) (Zx z)):= act_mul ..
       change Kin σ _ (fun z=>acts ((1+z i • Pz i)*_) (Zx z)); simp_rw[h]; apply Prefixe σ _ _ _ _ ht'
#print axioms Carry_p
end
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
