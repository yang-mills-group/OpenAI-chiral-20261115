import YM.SU5.May.TorqueBeam
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.TorqueBeam
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "Ω" => Complex.I
open May.Floe
open Buffered Buffered.Advance Buffered.Advance.Whorl May.Arctic
variable {K: Pressure.Teller group} {P: Patch}{B:Side}{e:ℝ}{Y: Pricing K.j P.L P.odd_side (Thread K.j)}(A:Grasp Y B e)(g:0≤e)(h:1≤K.j) (p:Pearl A) (u:Stamped K.j P.L P.odd_side Y)
variable {m:Side}(R:Ramp)(M:Jill.Male)(k:A.roundZ ≤ (CSide m B).val)(w:Pad K.j (CSide m B))
variable {α:Type*} (X:α→ Reader0 (Single (CSide m B)))
local notation "N"=> CSide m B
local notation "Σ"=> changeM (m:=m) A 1 M
local notation "U"=> R.vehicle (CSide m B)
local notation "S"=> Tset (CSide m B)
local notation "K₀"=> ledger (CSide m B) K.j M
noncomputable abbrev Harvest (N₀:Side)(X:α→ Reader0 (Single N₀)):= Sum.elim (send (R.vehicle N₀) ∘ X) X
variable {W:Finset (Single (CSide m B))}{ρ:ℝ} {x y: Reader0 (Single (CSide m B))}
include R p u w g h k M
omit R p u w g h k M in
lemma chargeable {b: Reader0 (Single (CSide m B))} (hx: withinM (if b.1 then Sᶜ else S) b.2): KeyT b (tickA (CSide m B)):=by rw [KeyT,touchP]; rcases b with ⟨⟨⟩,v⟩; exact hx; exact within_compl.mp hx -- remove include
omit R p u in
lemma thermo (hx:KeyT x (tickA N))(hy:KeyT y (tickA N)): SpinPrice Σ (ton x*ton y) = rankG K₀ x y:=by
 let P:Bool→ Reader0 (Single N):= fun b=> if b then x else y
 have ht:= Hygrometry.reckons M w.1 h (overhead A g k w M) P (fun i=>by cases i; exact hy; exact hx) [true,false]; rw [Hygrometry.duo] at ht; simpa [rollC, Function.comp,P] using ht
omit p u in
lemma track (hx:KeyT x (tickA N))(hy:KeyT y (tickA N)): promoted U K₀ 0 x y= Complex.I*SpinPrice Σ (theta U (ton x)*ton y):=by rw [mark_send, Matrix.smul_mul,SpinPrice.cash,thermo A g h M k w (markSend R hx) hy, fromRank]; ring -- args
lemma rear (hx:KeyT x (tickA N))(hy: KeyT y (tickA N)): costal x*costal y*rankG K₀ (send U x) (send U y)=star (rankG K₀ x y):=by
 rw [←thermo A g h M k w (markSend R hx) (markSend R hy)]
 -- tune simplified
 rw [←thermo A g h M k w hx hy,←spin_mirror A g h p u R M k,theta_mul,mark_send,mark_send]; simp only [Matrix.smul_mul,Matrix.mul_smul,SpinPrice.cash,mul_assoc]; ring
omit R p u w g h k M in
lemma charge_fine (b: Reader0 (Single (CSide m B)))(hv:KeyT b (tickA N)): Reed.Fine S Finset.univ true (ton b):= by
 have h : withinM (if b.1 then Sᶜ else S) b.2:=by rw [KeyT,touchP] at hv; cases p:b.1<;> simp only [p,Bool.false_eq_true,ite_false,ite_true,within_compl,withinM] at * <;> assumption
 exact (Worth.fine (A:=S) («S»:=Finset.univ) (ρ:=‖b.2‖) (x:=b) ⟨h,within_univ _,le_rfl⟩) -- param P name
lemma hermitian (hx:KeyT x (tickA N))(hy:KeyT y (tickA N)): star (promoted U K₀ 0 x y)= promoted U K₀ 0 y x:=by
 rw [track A g h R M k w hx hy,track A g h R M k w hy hx, star_mul',show star Ω= -Ω from Complex.conj_I,←spin_mirror A g h p u R M k, theta_mul, theta_twice U (R.pin_car N) (charge_fine x hx).sector]; have he: ton x*theta U (ton y)=(-1:ℂ) • (theta U (ton y)*ton x):= by
    have hg:Reed.Fine (Tset N) Finset.univ true (theta U (ton y)):=by
        rw [mark_send]; exact (charge_fine _ (markSend R hy)).scale _
    exact (charge_fine x hx).sign_com hg
 rw [he, SpinPrice.cash]; ring
-- turn now just real. norm-square $complex to ℝ x^2$, negative ticket.$δ` bound.
lemma coversHere (δ:ℝ) (v:∀ (b:Bool)(x:Ket (Single N)), withinM (if b then Sᶜ else S) x → withinM W x → -(δ*‖x‖^2) ≤ (promoted U K₀ 0 (b,x) (b,x)).re): WickPlate U K₀ δ S W:=by
 intro b x hy hx; let c:Reader0 (Single N):=(b,x); let D:= promoted U K₀ 0 c c; let Z:ℂ:= (↑δ:ℂ) * ↑(‖x‖^2)
 have hp: wickRay U K₀ b δ x x= D+Z:=by cases b<;> simp [D,c,Z,promoted, wickRay,inner_self_eq_norm_sq_to_K]
 have hg:= v b x hy hx; change -(δ*‖x‖^2) ≤ D.re at hg
 have he:star D=D:= hermitian A g h p u R M k w (chargeable (b:=c) hy) (chargeable (b:=c) hy); have ht:= congrArg Complex.im he; rw [hp, Complex.le_def]; simp [Z,pow_two] at *; constructor <;> linarith -- tune names @
#print axioms coversHere
end YM.CF.May.TorqueBeam
