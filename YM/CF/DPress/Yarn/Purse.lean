import YM.CF.DPress.Yarn.Nomad
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
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
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
open Chaff Gloss Maize Tye RP RP.Str Brace
open Source
variable {T : Source P_ J}{Jp:ℕ→ℝ→ℝ}
open Cap
local notation "hx'"=> hat R.L x
local notation "U♥"=> StarPS n
variable (Y:StarPS n)(hk:Beacon T F n Jp k)
local notation "β0" j:max=> BQ (k:=k) D Y j
local notation "Q1" => Jp
local notation "r_K"=> D.radiusX hk
local notation "GN" j:max=> apt M B R.L j
local notation "NeedY"=> need (k:=k) (Jp:=Jp) D
variable (Z : Lore M B R A.μ){Yc:VestM M B R}
local notation "A_"=> (ηD (A:=A))
variable (Lq: LedgerL D Z Y Yc)
abbrev μx (Λ:Thrift A)(x:ℝ)(k i:ℕ):ℝ:=ηD (A:=A)^(k-i)*(Λ.w (hat R.L x k)/4)
structure Born (Q:LogH (cell M B R.L i))(Yc: VestM M B R):Prop where
 leg: JStep D (ply_U R.L 1 (N:=cell M B R.L i)) Q.fuel (Λ.w (hat R.L x i))
 money : AccountY (Δ.a i) C.h (Q.fuel-(Yc i).fuel) (μx Λ x k i) -- implicit k used
local notation "μ'"=> μx Λ x k
local notation "η"=> ηD (A:=A)
local notation "Hx"=> hat R.L x
abbrev Chart(i:ℕ) (b:ℝ)(h:i<n):= Silo.Can (D.locale i h) P_ ((Λ.O (hat R.L x i)).δ) b -- package lean
include D
lemma τw (i:ℕ) : 0< Λ.w (hat R.L x i):= Λ.getW _ ▸ (F.epoch i).tax.Dust0.grant -- include F
lemma positiveμ (k i:ℕ): 0<μx Λ x k i:= mul_pos (pow_pos (ηpos (A:=A)) _) (div_pos (D.τw _) (by norm_num))
lemma posμ {v:ℕ}(h:v≤k):μx Λ x k v ≤ Λ.w (hat R.L x v)/4:=by
 let u:=ηD (A:=A); have he:u≤1:= Λ.he.trans (by norm_num); refine le_trans (b:=Λ.w (Hx k)/4) ?_ (div_le_div_of_nonneg_right (F.wealth h) (by norm_num)); exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (Thrift.ηpos (A:=A)).le he) (div_nonneg (D.τw k).le (by norm_num))).trans_eq (one_mul _)
lemma ξμ(v:ℕ)(p:v< k):μx Λ x k v=A.meter (μx Λ x k (v+1)):=by unfold μx Harvester.meter; rw [show k-v=k-(v+1)+1 from (by omega),pow_succ']; change (η* _) * _= η* _; ring
omit D
abbrev Swept (Z: Lore M B R A.μ):Prop:= ∀ i:ℕ,∀ s:Sweep (cell M B R.L i), ply_U R.L 1 s → (Z i).even s
variable (Zq:Swept Z)
lemma sweptStep (h:i<n) (w:Sweep (cell M B R.L (i+1)))(p:Maud.orderτ (apt M B R.L i) w): ply_U R.L 1 w:=by obtain ⟨x,rfl⟩:=p; exact ply_s (GN i) x R.L 0 (ply0 R.L x) rfl
include D Y hk Lq
lemma originh {X: LogH (cell M B R.L k)}(t:need (k:=k) (Jp:=Jp) D k X): Born (k:=k) (i:=k) D X Yc :=by
 unfold need at t; rw [Nat.sub_self] at t; let t0:= Tew.tiny R (Hx k); let Z':= F.epoch k; have h:= hk.h; let p₀:= (D.rank_none _ _).2 (Lq.paid k (by omega)); let E:=Jp 0 (Hx k); have x:JStep (i:=k) D Utrue X.fuel E:= (D.rank_none _ _).2 t; have hx:0<t0:= Z'.tax.Dust0.tiny; have hv:4*(t0+E) ≤ Λ.w (Hx k):=(hk.ok _ F.time).2; have he:0≤E:= D.alphaP0 hk 0 (by omega)
 constructor; · exact ⟨x.1.more C.uB (by linarith),x.2.small (fun _ _=>trivial)⟩
 rw [μx,Nat.sub_self,pow_zero,one_mul]; exact (AccountY.sub C.uB x.1.toAccountY p₀.1.toAccountY).more C.uB (by change E + t0 ≤ _; linarith only [hv])
lemma roomδ(i:ℕ):4*(Tew.tiny R (hat R.L x i))≤ Λ.w (hat R.L x i) :=by rw [Λ.getW]; exact (F.epoch i).tax.Dust0.strain
include Zq
local notation "μ@"=> Jp
local notation "XH'" j:max=> (Δ.a j)
local notation "x0" => hat R.L x i
-- Actual paired bonds expose witness α.S. Bound.$R*. Portfolio includes manuscript shift & line witness. positive factor uses period.
inductive Lodge (i:ℕ)(α:ℝ)(b:ℝ)(t v:LogH (cell M B R.L (i+1)))(u w:LogH (cell M B R.L i)):Prop
 | made (g:i<n)(L R':LobbyP D g b)(T:HonestL L)(P:HonestL R')(f:Lapse L R' (μx Λ x k (i+1)))(x0':t.fuel=L.F0)(x1:t.v=L.J)(u0:v.fuel= R'.F0)(u1:v.v= R'.J)(e:α=(D.σp i g).twin L T R' P)(ωξ:Can (D.locale i g) P_ (Λ.O (hat R.L x i)).δ α)(hL:u=postH D b L (Z i) 0 T (base0 (Λ.O (hat R.L x i)).pos))(hR:w=postH D b R' (Z i) α P ωξ): Lodge i α b t v u w
set_option maxRecDepth 6144 in
private lemma niece {w: LogH (cell M B R.L i)}(p:i<k){S: LogH (cell M B R.L (i+1))}{z:ℝ} (f:Lodge (k:=k) D Z i z (D.b_T Y (i+1)) (Yc (i+1)) S (Yc i) w):Born (k:=k) (i:=i) D w Yc:=by
 obtain ⟨g,Fv,Tb,T,W,vK,h1,h2,h3,h4,e,ωH,V0,FΔ⟩:= f; subst z; subst w; let X:= D.σp i g; let V:= X.twin Fv T Tb W; let f: Spell D Z i (D.b_T Y (i+1)) _ S _:= Spell.via g Tb W ωH h3 h4 (Eq.refl _); let v:= (f.valid D Z); constructor; · exact ⟨v.1.more C.uB (Λ.η_upper (D.τw i).le),v.2.small (fun s p=>Or.inr (Zq i s p))⟩
 have he:Silo.Can (D.locale i g) P_ _ _:= ωH
 rw [V0,D.ξμ i p]; exact Silo.ΔOKK (σp D i g) (Z i) Fv T Tb W vK (F.epoch i).tax.sponsors
set_option maxRecDepth 6144 in
private lemma rightΑ (p:i<k){S:LogH (cell M B R.L (i+1))}(v:Born (k:=k) (i:=(i+1)) D S Yc){g:i<n}(Fv:LobbyP D g (D.b_T Y (i+1)))(xq:(Yc (i+1)).fuel= Fv.F0):∃ E:LobbyP D g (D.b_T Y (i+1)), HonestL E ∧ Lapse Fv E (μx Λ x k (i+1))∧ S.fuel= E.F0 ∧ S.v=E.J:=by
 let b:=D.b_T Y (i+1); let P:= Λ.O x0
 have h2: Λ.w (Hx (i+1)) ≤ P.δ:= (F.wealth (Nat.le_add_right ..)).trans_eq (Λ.getW _)
 let U':LobbyP D g b:=⟨S.fuel,S.v,Fv.τ,v.leg.1.more C.uB h2⟩; let Tu:HonestL U':=v.leg.2.small (fun i v=> sweptStep g i v)
 have he:= smallU D (Lq.paid (i+1) g); have f:Lapse Fv U' (μx Λ x k (i+1)):=by
    rw [xq] at he; have hy:Tew.tiny R (Hx i) ≤ P.δ/2:=by have hv:4*Tew.tiny R (Hx i)≤ P.δ:=(F.epoch i).tax.Dust0.strain; have he:0≤P.δ:=P.pos; linarith
    refine ⟨D.positiveμ k (i+1), (D.posμ p).trans (div_le_div_of_nonneg_right h2 (by norm_num)),(he.1.toAccountY).more C.uB hy,(show AccountY _ _ (S.fuel-Fv.F0) _ from xq ▸ v.money)⟩

 exact ⟨U',Tu,f,rfl,rfl⟩
set_option maxRecDepth 6144 in
lemma cousin (p:i<k){S: LogH (cell M B R.L (i+1))} (v:Born (k:=k) (i:=(i+1)) D S Yc):∃ (Z':LogH (cell M B R.L i))(a:ℝ),Born (k:=k) (i:=i) D Z' Yc∧ Lodge (k:=k) D Z i a (D.b_T Y (i+1)) (Yc (i+1)) S (Yc i) Z':=by
 have g:i<n:=by have h:= hk.h; omega
 obtain ⟨e,Uc,L,t,xq,yq,Θq⟩:=Lq.step i g
 obtain ⟨P,v,f,pA,pS⟩:= rightΑ D Y hk Z Lq Zq p v Uc xq
 let c:= (D.σp i e).twin Uc L P v; let G:= (D.σp i e).passage Uc L P v f
 let w:= postH D (D.b_T Y (i+1)) P (Z i) c v G
 have hp:Lodge (k:=k) D Z i c (D.b_T Y (i+1)) (Yc (i+1)) S (Yc i) w:= Lodge.made e Uc P L v f xq yq pA pS rfl G Θq rfl
 exact ⟨w,c,niece D Y hk Z Lq Zq p hp,hp⟩
end Crib
end FitD
end YM.CF.Py.Kay
