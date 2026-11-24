import YM.CF.Vault.Laps
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n][Nonempty n]
variable {P Q W V K B R :Op n}
-- packaged fields. Kappa log of compressed map rather than normal orientation
abbrev train (P Q W C D:Op n):= straightC Q C D (throat P Q W)
def beard (P Q W C D:Op n)(k:ℕ):ℂ:= rockZ (train P Q W C D) Q k k
variable (C D: UNI n)(hC:C.valᵀ= -C.val)(hD:D.valᵀ= -D.val)(hP:det C.val=det D.val)
lemma glide_k (k:ℕ)(P Q W C D:Op n)(b:Bool)(U:UNI n)(h:Stay Q (train P Q W C D) k) : beard (sings b U P) (sings b U Q) (sings b U W) (congrC U (windX b C)) (congrC U (windX b D)) k=cSignX b (beard P Q W C D k):=by unfold beard train throat; rw [← singm, ← singm]; exact relayC b Q _ C D U U k h
lemma shade_k (k:ℕ)(C D:UNI n)(P Q W:Op n)(h:Stay Q (train P Q W C D) k)(p:sings true C P=P)(l:sings true D Q=Q)(he:D.val*cc W=W*C.val)(cD:congrC D (cc D.val)=D.val)(cP:congrC C (cc C.val)=C.val): beard P Q W C D k = star (beard P Q W C D k) :=by
 unfold beard train; let V:= throat P Q W; have ht:=relayC true Q V C.val D.val D C k h
 have hy:D.val*windX true V*star C.val=V:=by
    have h₁:= twist_product C (cc P); rw [show twist C (cc P)=_ from p] at h₁ -- tune
    have h₂:= twist_product D (cc Q); rw [show twist D (cc Q)=_ from l] at h₂
    change D.val*cc _ * _=_; unfold V throat; rw [cc_mul,cc_mul,←mul_assoc,←mul_assoc,← h₂,mul_assoc Q, he]; rw [←mul_assoc, mul_assoc _ C.val (cc P), ←h₁,← mul_assoc, mul_assoc _ C.val, C.property.2,mul_one] -- tune
 dsimp only at ht; rw [hy,l,show windX true C.val=cc C.val from rfl, show windX true D.val=cc D.val from rfl,cP,cD] at ht
 exact ht
lemma beamed {i:ℕ}(v:Clad P Q W V K)(B:Stay Q (train P Q W C D) i)(h:0 < i): acts (quant (throat P Q W)) (filled P C)= Complex.exp (beard P Q W C D i) • filled Q D ∧ filled Q D≠0:=by
 rw [boom v]; obtain ⟨u,K,-⟩:= B 0 h (berth i 0) ⟨le_rfl,ber_m i (by omega : 0 ≤ 0+1)⟩; have hf: train P Q W C D (berth i 0)=D.val:=by simp [train,straightC,berth0]
 rw [hf] at u K; refine ⟨(princess v.helm ?_ B h).symm,signs_nz v.helm u K⟩; unfold throat; rw [←mul_assoc,←mul_assoc, v.helm.isIdempotentElem.eq]
include hC hD hP
variable {A:Op n}
lemma pillow_k {i j:ℕ}{R R' K K':Op n}(t:Clad P Q W V K)(k:Clad (1-P) (1-Q) V W K')(g:Stay Q (train P Q W C D) i) (p:Stay (1-Q) (train (1-P) (1-Q) V C D) i)
 (S:Clad A A W V R)(T:Clad (1-A) (1-A) V W R')(v:Stay A (train A A W C D) j)(s:Stay (1-A) (train (1-A) (1-A) V C D) j)
 (h:0 < i)(l:0<j)(Y:UNI n)(ha: twist Y A=1-A)(hc:congrC Y C.val=C.val)(hd:congrC Y D.val=D.val)(hw:twist Y W=V): let y₁:=beard P Q W C D i; let y₂:=beard (1-P) (1-Q) V C D i; let w:=beard A A W C D j;
 Complex.exp (2*(y₂-w))=Complex.exp (2*star (y₁-w)):=by
 intro y u x
 have he:=beamed C D t g h; have hz:= beamed C D k p h; have hp:= beamed C D S v l; have hv':=beamed C D T s l
 have hx:= burnt t C D k hC hD he.1 hz.1 he.2 hP; have hv:=burnt S C D T hC hD hp.1 hv'.1 hp.2 hP
 have hb:beard (1-A) (1-A) V C D j=beard A A W C D j:=by
    have H:=glide_k j A A W C D false Y v; rw [singT,singT, show windX false A=A from rfl, show windX false W=W from rfl,ha,hw, show windX false C.val=C.val from rfl, show windX false D.val=D.val from rfl,hc,hd] at H; exact H
 rw [hb] at hv
 rw [two_mul,two_mul,Complex.exp_add,Complex.exp_add,←sq, ←sq, Complex.exp_sub, Complex.star_def,Complex.exp_conj,Complex.exp_sub];
 change (Complex.exp u/Complex.exp x)^2=(star (_/_))^2 -- tune star/div
 rw [div_pow,star_div₀,div_pow,hx,hv]; exact mul_div_mul_right _ _ (right_ne_zero_of_mul (hv ▸ pow_ne_zero 2 (Complex.exp_ne_zero _)))
end YM.CF.Vault
