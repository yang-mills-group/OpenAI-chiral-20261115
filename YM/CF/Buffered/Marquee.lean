import YM.CF.Buffered.Reruns
/-! Translating the coherency requests from + torus of the manuscript to q.

Do not need to compare (ember hypothesis) outside the given even ratios; don't need
any construction of the scrolls or lifts; just item Ember on actual partner selected to
emit; plus its actual offset. -/
set_option autoImplicit false
set_option maxHeartbeats 510000
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.Buffered.Mail
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Reflect Phase RP MeasureTheory
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Tenant Vale Skye Py Concert
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid Wilson
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m v p B l n k a b:Side}{e x:ℝ}
-- Receipts at the given seam support: symmetric equality under overlap.
variable {K:Ticket m v B p e x}{D:Ticket n v B l e x}{H:Ticket a v B k e x}
namespace Unison
lemma trans (f:Ticket.Coherent D H)(g:Ticket.Coherent K H): Ticket.Coherent D K:=by
 have hz:permitted D.K e x=permitted (B:=B) K.K e x:= (f.test D H).trans (g.test K H).symm
 exact ⟨fun i u=>(f.water ..).trans (g.water ..).symm, fun i u a=> (f.bill i u a).trans (g.bill i u (hz ▸ a)).symm,fun i u a=>(f.paint i u a).trans (g.paint i u (hz ▸ a)).symm⟩
variable {K:Calibration} {J:Tiling K}{C: Conveyor K}
structure Sponsor (K:Calibration) (C:Conveyor K)(J:Tiling K)(n:ℕ) where
 takes : K.takes (K.listTop n)
 history (m:Side)(p:K.Allowed m n): Bedded C p
 pin : Ticket (mesh (K.listTop n) K.R.L n) (mesh J.d' K.R.L n) K.B (J.qcount (K.listTop n)) K.e (topT K n) -- typically permit attached to Bedded or Shots at Top. not need equality criterion if Top not in cone
 offset (m k:Side)(p: K.Allowed m n)(t: Odd k.val)(h: K.listTop n=m*k): |starfare C m n-starfare C (K.listTop n) n/(k.val:ℝ)^4| ≤1  -- τ ≤1 price
 pressure (m k:Side)(p: K.Allowed m n)(t: Odd k.val)(b:K.listTop n=m*k)(h:Planck (mesh (K.listTop n) K.R.L n) (mesh m K.R.L n) k) : Mail.Ember h pin ((history m p).permit J)
variable (K)
lemma refK {i:ℕ}(p:K.takes (K.listTop i)) (b:K.Allowed m i)(j:ℕ)(t:K.listTop i=m*n): Planck (mesh (K.listTop i) K.R.L j) (mesh m K.R.L j) n:=by constructor; rw [t]; unfold Vale.mesh; push_cast; ring
variable {K}{r:ℕ}(Y: Sponsor K C J r)
local notation "Lq"=> K.q
include Y
private lemma tokenized (p: K.Allowed m r) : Ticket.Coherent ((Y.history m p).permit J) Y.pin :=by obtain ⟨k,u,w⟩:=p.2.1; exact Mail.sizes _ _ _ (Y.pressure m k p u w (refK K (b:=p) Y.takes r w)) -- tune
private lemma costK (p:K.Allowed K.q r)(g:K.Allowed m r)(h:m=Lq*k): |starfare C K.q r-starfare C m r/(k.val:ℝ)^4|≤2:=by
 obtain ⟨m',u,v⟩:= g.2.1; obtain ⟨j,t,A⟩:=p.2.1; have hp : j=k*m':= by apply mul_left_cancel (a:=Lq); rw [←A,v,h, mul_assoc]
 have e: 0 < (k.val:ℝ):= by positivity
 have hx:=Y.offset Lq j p t A; rw [hp] at hx; have he:= abs_le.mp hx; have hu:= abs_le.mp (Y.offset m m' g u v); push_cast at he
 have hy : (k.val:ℝ)≥1:=by exact_mod_cast k.property
 have hz: (k.val:ℝ)^4≥1:= one_le_pow₀ hy; rw [mul_pow] at he
 rw [abs_le]; constructor <;> field_simp at * -- horrific
 · apply le_of_mul_le_mul_right _ (by positivity : 0<(m'.val:ℝ)^4); nlinarith only [he.1, hu.2,mul_le_mul_of_nonneg_right hz (by positivity: 0≤(m'.val:ℝ)^4)]
 apply le_of_mul_le_mul_right _ (by positivity : 0<(m'.val:ℝ)^4); nlinarith only [he.2,hu.1,mul_le_mul_of_nonneg_right hz (by positivity: 0≤(m'.val:ℝ)^4)]
-- alternative receipts
noncomputable def book : Flipbook K J C r := ⟨Y.history,fun m h g=>trans (tokenized Y g) (tokenized Y h),fun _ _=>costK Y⟩
end Unison
end YM.CF.Buffered.Mail
#print axioms YM.CF.Buffered.Mail.Unison.book
