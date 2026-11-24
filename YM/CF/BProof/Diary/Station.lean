import YM.CF.BProof.Physical
import YM.CF.BProof.Diary.Time
import YM.CF.Py.Costs
import YM.CF.BProof.Start.Client
/- True history = eq:den. Make price on request of any period & such trajectory. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Diary
open Function Filter NormedSpace Finset
open Lattice Tenant Lat Cube Skye RG Wilson Push.SectorMeasure Precision
open Vale Vale.Grace Hom Py Paige Rush Scroll Scree Jet Vault Drapes
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Pressure
variable {N B : Side} {K : Teller SU.group} {P : Patch} {R : ChartRatio SU.group}
variable (V : Grace K P R) {d : ℝ} {F : Grasp V.U B d} {W : GivenX V F} {x : ℝ} (J : Robes N V W)
variable (M:Side) {N₀ : ℕ} (X : Month x 1 6 2 N₀ V W) (h : ℝ) (q : Chi) (R₀ δ : ℝ → ℝ)
local notation "L"=> P.L
local notation "m_"=> (M*N)
local notation "Φ"=> F
abbrev Np (j:ℕ) := cell m_ B L j -- alias _ notation requires binder V? implicits inferred N M P B only. avoid everywhere
local notation "Fχ"=> hat P.L
open Start
abbrev TimeSupport := Gates.Stage K.top.clip K.top.width K.top.paths V.W.bar
abbrev Tempo:= Spin.Ready K.j V.f V.g V.F1 V.F2
variable {a:ℕ}{u:ℝ}{D:Tempo V}(S:TimeSupport V)(E:Rhythm.Essence D u)(Δ:Rhythm.Note E (Gates.gap P.L a) J.n)(U:Start.Mote S E Δ F W.C.b W.C.B)
local notation "cellJ"=> cell (M*N) B P.L
variable {σ:ℕ}{i n:ℕ} {Y:Cape (M*N) B P.L}{ρ:ℕ→ℝ}
variable {V J E Δ S R₀ δ X h q U}
variable (T: Run V J X M h q R₀ δ n Y ρ)
local notation "dJ"=> T.D i
local notation "Υ"=> Y i
local notation "Vκ"=>K.top.clip
variable (t:Mote.Licence U Pressure.radiusB (Py.dleaf P.L) σ (hat P.L x i) h)
variable (hi: i≤n)(hp:0≤h)(vx:0<x)
include T hi hp vx
lemma head_order : 1 ≤ K.j := by have hh:= V.L.lobby; have ht:= P.order_cut; omega -- specialize buyT hV
lemma clients : Mote.BuyP (J:=U) (Γ:=t) (ν:=J.k) Υ dJ:=by
 let ε:=Py.dleaf L; let Z:= T.law; let A:=dJ; let Fβ:=hat P.L x i; have ht:0<Fβ:= vx.trans_le (Vale.crown P.L x i)
 have hh : (X.a i)= A.p := (Z.note.owns i hi).width; have hd: Vκ=A.funds:= (Z.note.owns i hi).fund; have hv:=J.gran.trans (Z.roof i).size
 have h0:= Z.roof i; let hP:Roof (cellJ i) J.k d J.n (Y i):= {h0.paid with paid:=fun t=>(h0.paid.paid t).shrink J.hr.le}
 have he: A.path.Bounds Vκ K.top.width K.top.paths V.W.bar:= by rw [show A.path=V.L.path (n-i) from (Z.note.owns i hi).path.symm]; exact V.L.mood _
 have hK: InterestX W.C _ A.J:= by rw [← (Z.note.owns i hi).taste]; exact (W.arm ..).sound i
 have hl:A.J.P.toll V.f V.g V.F1 V.F2:=by rw [←W.h1,←W.h2,←W.h3,←W.h4]; exact hK.leanJ.1
 have hz : Py.LotR A h (ε Fβ) (ε Fβ):= (Z.note.note i hi).lot_p le_rfl le_rfl -- tune namespace
 have e:Girt.Ward A:= Py.ward_m (hd ▸ he) hz
 have H:1≤ K.j:=by have hh:= V.L.lobby; have ht:= P.order_cut; omega
 have v:= X.boot i; have hr:(X.a i).threshold=thresh Fβ := v.1.trans (thresh_eq ht).symm; have p:=Z.note.sift i hi; have g':= Py.frostQ hz hp hK
 exact ⟨hh ▸ hr,hd.symm,hr ▸ Z.pole i,hP, ⟨(by have he:Fβ/2 ≤ (dJ).beta:=p.1; change Fβ ≤_; linarith),p.2⟩, he,hl,hK.leanJ.2.pay,Oasis.carrier g'.reg g'.slip g'.force,hv,hh ▸ v.2.1,hh ▸ v.2.2.1,⟨fun x g=> Girt.sweep A e hl Υ J.n hP x g W.pearl V.note hv H,Girt.sailW A e W.pearl V.note W.health H J.n Υ hP hv⟩⟩ -- Warp
end YM.CF.BProof.Diary
