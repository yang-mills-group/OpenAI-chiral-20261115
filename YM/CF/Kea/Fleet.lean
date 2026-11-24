import YM.CF.Kea.Laze
import YM.CF.Spire.Thick
import YM.CF.Reflect.Regular
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Kea
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill SU Rush Tulip Cube Fock Peaks Dial Spire Vault Scroll Paige Brace
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {L B m:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e:ℝ}{P:Grasp Y B e}
lemma concur (A:Pearl P)(S:Stamped j L ho Y)(p:0<e)(h:1 ≤ j)(W:Jill.Male)(t:P.roundZ ≤ (CSide m B).val): Continuous (fun i:CapX m B e=> changeM P i.val W):=by
    obtain ⟨_,_,_,_,T⟩:= cycle A S p h 0 1 le_rfl; obtain ⟨F,U,H,V,v⟩:= T m t W
    let L:=chant m B j W (P.cost m W); have he:Continuous (fun i:CapX m B e=>L i.val):= continuousOn_iff_continuous_restrict.mp (freezing P.topB P.baseY.1 (P.couture t W) (P.broadness _ t W).continuousOn)
    let K:=candle m B (P.cost m W); have hp:Continuous (fun i:CapX m B e=> K i.val):=by rw [funext v]; exact continuous_finsetSum _ fun i _=>(H i).cont
    exact (Complex.continuous_exp.comp hp.neg).smul he

def allC:Signed:= Signed.mirror 0 * Signed.mirror 1 * Signed.mirror 2 * Signed.mirror 3
lemma whirl(a:Axis): (posDir a).rotate allC=negDir a:=by fin_cases a <;> decide
lemma all_d:detX allC=false:=by simp only [allC,det_p,det_t]; rfl
lemma ar_abs(x:TF): polarX true ((waveG x)⁻¹)=waveG x:=by apply fund_inj; rw [polar_val,SU.fund_inv,wave_id]; ext a b; change star (star (Matrix.diagonal (pw∘x.val) b a)) = _; rw [star_star]; by_cases h:a=b <;> simp [h,Ne.symm]
def hazel: Shape:=⟨allC,0⟩ -- inspect
lemma glazeV (d:Candle)(N:Side):stir (xtra true) hazel (tax d (N:=More N))=tax d:=by
 funext i; obtain ⟨i,a⟩:=i; unfold stir; simp only [Function.comp_apply,Lattice.pull,show hazel.s=allC from rfl,whirl,Step.neg_read]; exact ar_abs _
variable (A:Pearl P)(S:Stamped j L ho Y)(t:P.roundZ ≤ (CSide m B).val)(p:1≤j)(d:Candle)(M:Jill.Male)
abbrev AMP (m:Side)(P:Grasp Y B e)(d:Candle)(M:Jill.Male):=inner ℂ (mateK (CSide m B)) (changeM P (tax d) M)
include A S t p
lemma absol(k:0<e): star (AMP m P d M)=AMP m P d M:=by
 obtain ⟨U,hU⟩:= det_sub true allC; rw [all_d] at hU; let K:= prepU hazel U (xtra true) (CSide m B); let X:=Tset (CSide m B); let W:=mateK (CSide m B); let R:=changeM (m:=m) P (tax d) M
 have hp: arum K true false W R=R:=by unfold R; rw [show arum K true false W _= _ from change_g A S t p _ (tax_guard d _ _ k.le) M _ true U hU,glazeV] -- hazel definitional
 have ht := arum_globe K true false X (touchP (CSide m B) ▸ tickB (CSide m B)) (tickR hazel (xtra true) U hU (CSide m B)) W R
 change inner ℂ (arum K true false (mateK (CSide m B)) W) (arum K true false _ R) = star (AMP m P d M) at ht
 rw [hp,show arum K true false _ W=W from arum_self K true false X (touchP (CSide m B) ▸ tickB (CSide m B)) (tickR hazel (xtra true) U hU (CSide m B))] at ht
 exact ht.symm
omit A S t p
lemma phase_cont : Continuous pw:=by unfold pw BZ.phase; fun_prop
lemma weave_cont:Continuous waveG:=by
 apply Continuous.subtype_mk; apply Continuous.subtype_mk; apply continuous_matrix; intro i j; by_cases h:i=j
 · change Continuous fun x:TF=> Matrix.diagonal (pw ∘ x.val) i j; rw [h]; simp only [Matrix.diagonal_apply_eq,Function.comp_apply]; exact phase_cont.comp ((continuous_apply _).comp continuous_subtype_val)
 change Continuous fun x:TF=> Matrix.diagonal (pw ∘ x.val) i j; simp [h]; exact continuous_const
lemma tax_cont(N:Side):Continuous (tax (N:=N)):= continuous_pi fun i=> weave_cont.comp (continuous_apply i.2)
include A S t p
set_option maxHeartbeats 280000 in
lemma vol_c(k:0<e):Continuous (fun i:Candle=>AMP m P i M):=by
 let f(i:Candle):CapX m B e:=⟨tax i,tax_guard i _ _ k.le⟩
 have ht:Continuous f:=(show Continuous f from Continuous.subtype_mk (tax_cont (Domain m B)) (fun i=>tax_guard i _ _ k.le))
 let Y0:=fun i:CapX m B e=>changeM P i.val M; let c:CapX m B e→ℂ:=fun i=>inner ℂ (mateK (CSide m B)) (Y0 i); have hl:Continuous c:= (continuous_const (y:=mateK (CSide m B))).inner (show Continuous Y0 from concur A S k p M t) -- tune Nat etc
 have he:(fun i:Candle=>AMP m P i M)=c∘f:=funext fun _=>rfl
 rw [he]; exact hl.comp ht
end YM.CF.Kea
