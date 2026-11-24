import YM.CF.Fir.Cue
import YM.CF.Lattice.Bare
import YM.CF.Cubes.Refine
/-! Antiperiodic quasi-waves over cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {N F : Side}

def mel (k:Site N): Momentum := tmap (pm k)
lemma mel_h (k:Site N): mel k ∈ baseCube := ⟨tmap_physical _,fun i=>abs_le.mpr ⟨(pm_zone k i).1.le,(pm_zone k i).2⟩⟩
lemma mel_away (k:Site N): mel k≠0:=fun h=> pm_nonzero k (funext fun i=> by
  have hx:=congrArg Complex.re (congr_fun h i); change (pm k i)=_ at hx; exact hx)

def natural (x:Site N) : Cover := fun i => (x i).val
lemma nat_true (x:Site N): wrap N (natural x)=x:=by ext i; simp [wrap,natural]
lemma freq_mode (k x:Site N): mode (mel k) (natural x)=frequency k x:=by
  unfold frequency mode
  rw [Finset.mul_sum,Complex.exp_sum]; apply Finset.prod_congr rfl; intro i _; unfold natural mel BZ.phase tmap; push_cast; rw [← Complex.exp_nat_mul]; congr 1; ring

def periods (N:Side)(f:Cover): Cover:= fun i => f i / N.val
lemma carrying (N:Side)(f:Cover): natural (wrap N f)+N.val • periods N f=f:=by
  funext i; simp only [natural,wrap,periods,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; rw [ZMod.val_intCast]; exact Int.emod_add_mul_ediv .. -- check cast

def fee (f:Cover) : ℂ := ∏ i, (-1:ℂ)^(f i)
def wind (x : Site N)(f:Cover): ℂ:= fee (periods N (natural x+f))
lemma fee_real (f:Cover): star (fee f)=fee f:=by simp [fee]
lemma fee_one (f:Cover): fee f*fee f=1:=by unfold fee; rw [← Finset.prod_mul_distrib]; simp_rw [← mul_zpow]; simp
lemma fee_norm (f:Cover): ‖fee f‖=1:=by
  have he:=congr_arg (‖·‖) (fee_one f); rw [norm_mul,norm_one] at he; nlinarith [norm_nonneg (fee f)]
lemma mode_fee (k:Site N)(f:Cover): mode (mel k) (N.val • f) = fee f := by
  unfold mode fee; rw [Finset.mul_sum,Complex.exp_sum]; apply Finset.prod_congr rfl; intro i _
  rw [show Complex.I * _=(f i:ℂ)*(N.val*(↑(principal (k i))*Complex.I)) by simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast]; unfold mel pm tmap; dsimp; ring]
  rw [Complex.exp_int_mul,Complex.exp_nat_mul, show Complex.exp (_*_) = BZ.phase (principal (k i)) from rfl,wind_eq,wind_p]
lemma wave_advance {p:Momentum}(hf:∀ f:Cover,mode p (N.val • f)=fee f)(x: Site N)(f:Cover):
   wind x f * mode p (natural (x+wrap N f))= mode p (natural x)*mode p f:=by
  unfold wind
  rw [←mode_shift p,← hf,mul_comm, ← mode_shift] -- maybe reorder
  congr 1; have he:= carrying N (natural x+f); rwa [map_add,nat_true] at he
lemma freq_advance (k x:Site N)(f:Cover): wind x f*frequency k (x+wrap N f)=frequency k x*mode (mel k) f := by simp_rw [← freq_mode]; exact wave_advance (mode_fee k) _ _
variable (G: Ratio N F)
abbrev stroll := G.count
lemma alias_fee (k:Site N)(l:Site G.count)(f:Cover): mode (aliasAt (mel k) l) (F.val • f)=fee f:=by rw [G.exact_size,mul_comm N.val,mul_smul,← mode_scale, alias_scale,mode_phase,mode_periodic,mul_one,mode_fee]
/-- root shifts align fine fermion nodes at odd gauge sites. -/
def offset (L: Side) : Cover:=fun _=>mid L
def isle : (Site N × Site G.count) ≃ Site F := G.splitSites.symm.trans (Equiv.addRight (wrap F (offset G.count)))
lemma isle_apply (x r): isle G (x,r)= G.embed x+wrap F (lift r)+wrap F (offset G.count):= rfl
lemma data_isle (ho:Odd G.count.val)(x:Site N)(r:Site G.count): natural (isle G (x,r))= G.count.val • natural x+lift r+offset G.count :=by
  let L:= G.count; let f:=L.val • natural x + lift r+offset L
  have hh : isle G (x,r)=wrap F f:=by rw [isle_apply, show G.embed x= wrap F (L.val • natural x) by
                                            rw [← G.embed_wrap,nat_true]]; simp only [f,map_add]; rfl
  rw [hh]; funext i; change natural (wrap F f) i=f i
  have hk:= centers_odd r ho i; have hv:= mid_double L ho; have hd:=G.exact_size
  have hx:0≤natural x i ∧ natural x i+1≤ N.val:= ⟨Int.natCast_nonneg _,by unfold natural; have h:=ZMod.val_lt (x i); omega⟩
  have hs:f i=L.val*natural x i+lift r i+mid L:= rfl -- nsmul issue
  have hL : (0:ℤ)<L.val:= by exact_mod_cast L.property
  change -(L.val:ℤ)+1 ≤ _ ∧ _≤ (L.val:ℤ)-1 at hk
  have hb:0≤f i∧f i<F.val:=by rw [hs,hd,Nat.cast_mul]; change _∧_<(N.val:ℤ)*L.val; constructor <;> nlinarith [hk.1,hk.2,hx.1,hx.2]
  change (ZMod.val ((f i:ℤ):Per F):ℤ)= _; rw [ZMod.val_intCast,Int.emod_eq_of_lt hb.1 hb.2]
lemma mode_isle (ho:Odd G.count.val)(x:Site N)(r k l):
    mode (aliasAt (mel k) l) (natural (isle G (x,r)))=frequency k x*mode (aliasAt (mel k) l) (lift r)*mode (aliasAt (mel k) (l:Site G.count)) (offset G.count):=by
  rw [data_isle G ho,mode_shift, mode_shift,←mode_scale,alias_scale,mode_phase,mode_periodic,mul_one,freq_mode]
def ratio : Ratio (Cube.More N) (Cube.More F):= ⟨G.count,by rw [show (Cube.More F).val=F.val*2 from rfl,G.exact_size]; change _=N.val*2*_; ring⟩
lemma embed_node (ho:Odd G.count.val)(x: Site N)(r:Site G.count): Cube.node (isle G (x,r))=(ratio G).embed (Cube.node x)+wrap _ (2 • lift r):=by
  obtain ⟨x,rfl⟩ : ∃ z,wrap N z=x:= ⟨natural x,nat_true x⟩
  let F1:Cover:=fun _=>1
  have he (N:Side)(x:Cover) : Cube.node (wrap N x)=wrap (Cube.More N) (2 • x+F1):=by rw [Cube.node,Ratio.root_embed,Ratio.embed_wrap,map_add,show wrap (Cube.More N) F1=1 by ext; change ((1:ℤ):Per _)=(1:Per _); simp]; rfl
  rw [isle_apply,Ratio.embed_wrap, ← map_add, ← map_add, he,he,Ratio.embed_wrap,←map_add]
  congr 1; funext i; simp only [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,offset,F1, ratio]
  have hh:=mid_double _ ho; simp only [Pi.mul_apply,Pi.add_apply,Pi.natCast_apply,Pi.ofNat_apply,F1,offset]; push_cast; nlinarith
end YM.CF.Rush
