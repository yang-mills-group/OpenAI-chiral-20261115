import YM.SU5.FiniteGaugeData.Celeritas.ChargeH
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T₁: Finset Cover)(s i k:ℕ)
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace Celeritas
open KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
variable (H:Harbor Y h W' R Φ a)(x y:Decko Y h a)
local notation "Λ₀"=> (A a)
namespace Land
open Mist Dover
variable (X:Engine Y h W' R a H)(q:Carousel Λ.R.L)(b:Axis)(B:List Axis)
variable (V:∀ a:Axis,Harbor Y h W' R Φ a)(T:∀ a:Axis,Engine Y h W' R a (V a))
open Mist Dover Leda
open scoped NNReal ENNReal
include S'
abbrev Wave (i:Axis):= TipH Y h W' R i (V i) (T i)
local notation "Θ"=> Wave Y h W' R V T
abbrev Osc (i:Axis):= casin Y h W' R A S' i (V i) (T i)
abbrev Φω (i:Axis):= Dew Y h W' R i (V i) (T i)
local notation "Ε" => Osc Y h W' R A S' V T
local notation "Ω"=> Φω Y h W' R V T
omit S' in
lemma trip_leg (a:Axis)(F:Hilbert)(G:E4→F.Op)(p:∀ x y,G (x+y)=G x*G y)(q:∀ x:ℝ,G (x • basis a)=1)(x:E4): G (x-x a • basis a)=G x:=by rw [sub_eq_add_neg, ← neg_smul,p,q,mul_one]
lemma leg_clock(x:E4) : leg ((Ε) a) x =combT Y h W' R a (V a) (T a) x Terrace.scheduleL:=by
 let Tc:=T a; exact trip_leg a ((Θ) a) (combT Y h W' R a (V a) Tc · Terrace.scheduleL) (by intro x y; exact comb_comp Y h W' R a (V a) Tc Terrace.scheduleL x y) (fun x=> (Kodiak.comb_one (whimsy Y h W' R a (V a) Tc) x a).trans (unit_flow Y h W' R a (V a) Tc x)) x
-- passport.B check supports after marker camera.Real.Lified boxes θ widths per axis. 
structure Cask where
 /- lean kernel if include contamination check. -/
 s : ℕ
 m : W (tent Y h)
 d : Axis→ℕ
 p : ∀ i,0<d i
 w : ∀ i,Plan Y h i (d i) m
variable (P':Cask Y h)
#check Cask
omit S' in
abbrev halfC (i:Axis):ℝ≥0:= thetaX Λ P'.s (P'.d i)/2
omit S' in
def youth := WithLp.toLp 2 (fun i:Axis=>(halfC Y h P' i:ℝ))
abbrev old (i:Axis) : (Wave Y h W' R V T i).Op:= Hills.social (Anteroom (T i).val) (bitOp Y h (P'.s) W' R A S' i (P'.d i) (V i) (P'.w i) (P'.p i))
def leafP :Shrine (Θ):= {
 t:= halfC Y h P', f:= fun i=> opt (Ε i) (-(youth Y h P')) (old Y h W' R A S' V T P' i)
  }
variable {σ:Type}(x:σ→Cask Y h)(y:σ→ E4)
def past(i:σ):E4:= y i-youth Y h (x i)
local notation "μ" i:max=> (x i).s
local notation "ν" i:max a:max => (x i).d a
local notation "C"=> past Y h x y
local notation "V'" => leafP Y h W' R A S' V T ∘ x
local notation "T'" => Hi (V') y
-- only needs any specific axis. tight.
lemma former (i:σ) : (past Y h x y i) a= startX (V') y a i := rfl
lemma foremost (i:σ) : (past Y h x y i) a+office (Λ:=Λ) (fun i=> μ i) (fun i=> ν i a) i=endX (V') y a i:=by
 rw [former Y h W' R A S' a V T]; unfold startX endX office; rw [← trackT Λ]; let q:=thetaX Λ (μ i) (ν i a); let Q:=(V' i).t a; have he:(q:ℝ)=↑Q+↑Q:=by rw [← NNReal.coe_add,show Q=q/2 from rfl,add_halves]
 change _-(Q:ℝ)+q=_+(Q:ℝ); rw [he]; ring
local notation "Z"=> (C) -- step
abbrev screenP {σ:Type}(x:σ→E4):Grid σ ℝ:=fun i a=>x i a
lemma expect_s (i j:σ) : SteamV Y h W' R a (V a) (T a) (fun i=> μ i) (fun a i=> ν i a) (screenP (C)) i j = ((Ε a).E (Hi (V') y a i j))*leg (Ε a) ((C) j-(C) i):=by
 rw [leg_clock]; unfold SteamV Hi; refine congrArg₂ (·*·) ?_ rfl; apply congrArg (fun i=> (Ε a).E (Real.toNNReal i)); rw [←former Y h W' R A S' a V T x y j, ← foremost Y h W' R A S' a V T x y i]; change (C j) a-(C i) a -_= _; ring
lemma earn_of (i:σ) : actO Ε (V') y a i=opt (Ε a) ((C) i) (old Y h W' R A S' V T (x i) a):= opt_add .. -- defeq
-- state layout.Aspect proof.Normalized to absolute support.Scalar.D.
variable (M:List σ)(τ:Axis→Prop)(κ:τ a)
local notation "D₁" a:max U:max=> picture Y h W' R A S' a V T (fun i=> μ i) (fun a i=> ν i a) (fun a i=>(x i).p a) (fun i=>(x i).m) τ (fun a _ i=>(x i).w a) U
lemma priced : chorus Ε Ω (V') y M a = (D₁ a M) κ (screenP (C)):=by
 classical
 let H':=V a; let F:=T a; let J:=(Wave Y h W' R V T a); let Z' (i:σ):= old Y h W' R A S' V T (x i) a
 let P(i j:σ):= Hi (V') y a i j; let G (F:J.Op):=inner ℂ ((Ω) a) (F ((Ω) a)); let w(i j:σ):= (Ε a).E (P i j); have hp:=ledger (C) (Ε a) Z' P ((Ω) a) (dew_pays Y h W' R A S' a (V a) (T a)).2 M
 have hx:chorus Ε Ω (V') y M a=_:=congrArg G (show TapeT (actO Ε (V') y a) (Leap Ε (V') y a) M=TapeT (fun i=>opt (Ε a) ((C) i) (Z' i)) w M from Hike.same_tape _ _ _ _ M (fun i _=> earn_of ..) (fun _ _ _ _=>rfl)); refine (hx.trans hp.symm).trans (Eq.symm ?_)
 exact congrArg G (Hike.same_tape (fun i=> carriesR Y h W' R A S' a V T (fun i=> μ i) (fun a i=> ν i a) (fun a i=>(x i).p a) (fun i=>(x i).m) τ (fun a _ i=>(x i).w a) i κ) Z' (SteamV Y h W' R a H' F (fun i=> μ i) (fun a i=> ν i a) (screenP (C))) (fun i j=> w i j*leg (Ε a) ((C) j-(C) i)) M (fun _ _=>rfl) (fun i _ j _=> expect_s ..)) -- annotate
section
variable (Z1:Axis→List σ)(p: M.Perm (Z1 a))
lemma Cusp (r: (Z1 a).Pairwise (Seers (V') y a)) : (screenP C)∈Leda.Space (Z1 a) (fun i a=>office (Λ:=Λ) (fun i=> (x i).s) (fun i=>(x i).d a) i) a:=by
 refine r.imp ?_; intro i j p'; change (C i) a+_<(C j) a; rw [foremost Y h W' R A S' a V T,former Y h W' R A S' a V T]; exact p'
-- pair $Z' order discr
variable (U:τ b)
include U κ
lemma comport (Dq:(Z1 a).Nodup)(e: Dover.Accord a τ Z1)(u:∀ i,τ i→ (Z1 i).Pairwise (Seers (V') y i)): chorus Ε Ω (V') y (Z1 a) a= chorus Ε Ω (V') y (Z1 b) b := by
 let hq(i:Axis)(p:τ i):=priced Y h W' R A S' i V T x y (Z1 i) τ p; rw [hq a κ,hq b U]; exact Dover.coincide Y h W' R A S' a b V T (fun i=>(x i).s) (fun a i=>(x i).d a) _ _ τ _ Z1 κ U e Dq _ fun i g=> Cusp Y h W' R A S' i V T x y Z1 (u i g)
-- includes κ U explicitly because goal types not referencing. 
#print axioms comport
end
section
variable (b':b≠a) (L:List σ)
include b'
lemma foible (u:M.Nodup)(v: M.Perm L)(k:M.Pairwise (Seers (V') y a))(K:L.Pairwise (Seers (V') y b)) : chorus Ε Ω (V') y M a =chorus Ε Ω (V') y L b:=by
 let τ'(i:Axis):Prop:= i=a∨i=b; let U' :τ' a:=Or.inl rfl; have hp:τ' b:=Or.inr rfl; let A'(i:Axis):=if i=b then L else M; have he:(A') a=M:= if_neg b'.symm; have hg:(A') b=L:=if_pos rfl; rw [← he,←hg]; refine comport Y h W' R A S' a b V T x y τ' U' A' hp (he.symm ▸ u) ⟨?_⟩ ?_; -- order κ and A'? tune
 · rintro i (rfl|rfl); exact List.Perm.refl _; rw [he,hg]; exact v
 rintro i (rfl|rfl); rw [he]; exact k; rw [hg]; exact K
end
#print axioms foible
end Land
end Celeritas
end YM.CF.Buffered.Afterglow.Hierarchy
