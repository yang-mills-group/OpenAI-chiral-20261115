import YM.CF.Buffered.Melody
import YM.CF.Buffered.Bouillon
/-! Plot-ready representation at a toron, summed over actual generation-0
color. Reassemble from SAME tax-link FIELD, retaining every character.
 Uses momentum span v after growth. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{F K T D U:Op (Single N)} {d:Candle}
namespace Lead
variable (A:Lead R)
def lasting (V:Pane N) (L:Op (Single N)) := sing R A.wave • ∑ p∈ five, ∑ q∈ five, (A.coil V p q) • (iceT L (true,A.lower N q) * iceT L (false,A.upper N p))
lemma dress_m (V: Pane N)(p:Clad F K T D U): Dress (laneP K T U) (A.birthOp V) (A.lasting V (laneP K T U)):= by
 apply Dress.l; refine Dress.sum _ fun i _=> Dress.sum _ fun j _=> Dress.l ?_ _; exact (depart p (true,A.lower N j)).mul (depart p (false,A.upper N i))
lemma lasting_z (V:Pane N) : A.lasting V 0=A.birthOp V:=by unfold lasting birthOp; simp [iceT,creed]
lemma laps_t (V:Pane N) : A.laps V=Lattice.travel V (node (wrap N A.birth)) A.traceV:=by rw [laps,onC,travel_at,add_zero,node_of]
private lemma fee_tr (d:Candle) (p q:Slot) : A.coil (N:=N) (Kea.tax d) p q=if p=q then newm d A.death p*star (newm d A.birth p) else 0:=by
 unfold coil; rw [laps_t,travD,Matrix.diagonal_apply]
 congr 1; have he:stop (0:Cover) A.traceV= 2 • (A.death-A.birth):=by
   have hx:=stop_trans (nodeC A.birth) 0 A.traceV; rw [add_zero,A.moves] at hx; unfold nodeC at hx; rw [smul_sub]; abel_nf at *; -- tune
   linear_combination (norm:=abel) -hx
 rw [he, newm, newm,← Emu.rho_m _ (tmap_physical _), ←mode_scale]; congr 1; funext i; rw [Pi.smul_apply]; simp only [tmap,rise,Pi.add_apply,two_smul, Complex.ofReal_add] -- tune
private def personA(d:Candle)(R:ℕ) := fun i:TagT=> nac (0:Site N) (Kea.tax d) 1 R i
abbrev endTag(A:Lead R)(p:Slot) : TagT := (A.death,⟨dnSpin A.slot,p,1⟩)
abbrev startTag(A:Lead R)(p:Slot) : TagT := (A.birth,⟨upSpin A.slot,p,1⟩)
def upperT (N:Side) (d:Candle) (p:Slot) := personA (N:=N) d R (A.startTag p)
def lowerT (N:Side) (d:Candle) (p:Slot) := personA (N:=N) d R (A.endTag p)
lemma upperF (p:Slot)(d:Candle)(N:Side): (A.upperT N d p).1=false := by simp [upperT,nac,personA, signW, up_half]
lemma lowerF (p:Slot)(d:Candle)(N:Side): (A.lowerT N d p).1=true := decide_eq_true (dn_half A.slot)
private lemma projected (d:Candle)(z: Cover)(p:Slot)(k:SpinIdx):hint (0:Site N) z ⟨k,p,1⟩ (Kea.tax d) 1=star (newm d z p) • basisC N z k p:=by
 rw [Emu.tax_f,basisC,smul_smul]; unfold Emu.hub Rush.wind; change (Rush.fee _* star _) • basisKet ((0+wrap N z,k),p)= _; rw [show natural (0:Site N)=0 by funext j; simp [natural],zero_add,zero_add,mul_comm]; rfl
lemma lower_t (d:Candle)(L:Op (Single N))(p:Slot) : iceT L (A.lowerT N d p)= -(star (Emu.gain R)*newm d A.death p) • iceT L (true,A.lower N p):= by
 unfold lowerT personA nac; dsimp only; simp only [signW,dn_half, decide_not, decide_false,Bool.not_false,ite_true,projected,iceT]; simp only [map_neg, map_smul]; change Fock.remove (-(Emu.gain _ • (star _ • _)))=_; unfold Fock.remove; simp only [map_neg, map_smul,star_smul,star_neg, neg_smul,smul_smul]; rw [star_mul,star_star,mul_comm (newm _ _ p)]; rfl
lemma upper_t (d:Candle)(L:Op (Single N))(p:Slot) : iceT L (A.upperT N d p)=(Emu.gain R*star (newm d A.birth p)) • iceT L (false,A.upper N p):= by
 unfold upperT personA nac; dsimp only; simp only [signW,up_half, not_true_eq_false,decide_false,Bool.false_eq_true,ite_false,projected,iceT]; simp only [map_smul]; change create (Emu.gain _ • (star _ • _))=_; rw [map_smul,map_smul,smul_smul]; rfl

def vocal (d:Candle)(L:Op (Single N))(p:Slot) := iceT L (A.lowerT N d p)*iceT L (A.upperT N d p)
abbrev cash (b:Bool) : ℂ:= (phaseF b:ℂ)/5
lemma open_mic (L:Op (Single N)) (d:Candle) : A.lasting (Kea.tax d) L= cash A.wave • ∑ i∈five, A.vocal d L i:=by
 unfold lasting; simp_rw [smul_sum]; apply sum_congr rfl; intro i hi; rw [sum_eq_single_of_mem i hi]; swap; · intro j _ h; rw [fee_tr,if_neg h.symm,zero_smul, smul_zero]
 rw [fee_tr,if_pos rfl, vocal,upper_t,lower_t, Matrix.smul_mul, Matrix.mul_smul]; simp only [smul_smul]; congr 1
 unfold sing cash
 have he: star (Emu.gain R)*Emu.gain R=(R:ℂ)^3:=by simp only [Emu.gain,Complex.star_def,Complex.conj_ofReal]; norm_cast; rw [←sq,Real.sq_sqrt (by positivity)] -- tune
 generalize newm d A.death i=f; generalize star (newm d A.birth i)=g; linear_combination he * (phaseF A.wave:ℂ)/5*f*g -- tune
lemma solo_mic (d:Candle) {K:Op (Single N)}(g:Clad F (Dial.tickA N) T D K)(p:Slot) : let V:=laneP (Dial.tickA N) T K; A.vocal d V p (Tset N) (Tset N)=rankG V (A.lowerT N d p) (A.upperT N d p):=by
 intro V; let f:=personA (N:=N) d R; have he:= vase g (Dial.tickB N) f (fun _=>nac_k ..) [A.endTag p,A.startTag p]
 rw [← Cache.mateV_emit (A.vocal d V p)]; unfold vocal
 rw [show iceT _ _ * iceT _ _=rollC (iceT V ∘ f) [A.endTag p,A.startTag p] from (by simp only [rollC,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl)]
 change inner ℂ (Dial.mateK N) (chime (iceT V ∘ f) (Dial.mateK N) [A.endTag p,A.startTag p])=_ -- defeq product one?
 rw [he]; simp [runes,claps,picks,spinC,offer,besideX,Fock.cval,cites,extendsU]; rfl
private lemma wick₂ {T : Type*}(d : T→T→ℂ)(p q r s : T) : runes d [p,q,r,s]= d p q*d r s-d p r*d q s+d p s*d q r:=by
 simp [runes,claps,picks,spinC,offer,besideX,cites,Fock.cval,extendsU,beside]; ring
private lemma rank_flip (F:Op (Single N))(u v:Reader0 (Single N)) : rankG F u v= -rankG F v u:=by unfold rankG; cases h:u.1 <;> cases p:v.1 <;> simp
abbrev note (A W:Lead R)(L:Op (Single N))(d:Candle)(p q:Slot) := rankG L (A.lowerT N d p) (W.upperT N d q)
lemma reserve (d:Candle) (W:Lead R) {K:Op (Single N)}(g:Clad F (Dial.tickA N) T D K)(p q:Slot) : let V:=laneP (Dial.tickA N) T K
 (A.vocal d V p * W.vocal d V q) (Tset N) (Tset N)= A.note A V d p p * W.note W V d q q-A.note W V d p q*W.note A V d q p:=by
 intro V; let f:=personA (N:=N) d R; let L:List TagT:= [A.endTag p,A.startTag p,W.endTag q,W.startTag q]
 have he:= vase g (Dial.tickB N) f (fun _=>nac_k ..) L
 rw [← Cache.mateV_emit (A.vocal d V p * W.vocal d V q)]; unfold vocal
 rw [show iceT V _ * iceT V _ * (iceT V _*iceT V _) = rollC (iceT V ∘ f) L from (by unfold L rollC; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,mul_assoc]; rfl)]
 change inner ℂ (Dial.mateK N) (chime _ _ _)=_; rw [he]; dsimp only [L]; rw [wick₂]
 change A.note A V d p p * W.note W V d q q - rankG V (A.lowerT N d p) (W.lowerT N d q) * rankG V (A.upperT N d p) (W.upperT N d q)+_=_
 rw [show rankG V (A.lowerT N d p) (W.lowerT N d q)=0 from if_pos (by rw [lowerF,lowerF]),show rankG V (A.upperT N d p) (W.upperT N d q)=0 from if_pos (by rw [upperF,upperF])]
 change _ - 0*0 + A.note W V d p q*rankG V (A.upperT N d p) (W.lowerT N d q)=_
 rw [rank_flip V (A.upperT N d p)]; simp only [zero_mul,neg_zero, add_zero,mul_neg,sub_eq_add_neg]
end Lead
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Lead.open_mic
#print axioms YM.CF.Buffered.Ballad.Lead.reserve

-- additional access for convergence
noncomputable section
namespace YM.CF.Buffered.Ballad.Lead
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
lemma note_hop {R:ℕ}{N:Side}(A W:Lead R)(d:Candle)(V:Op (Single N))(p q:Slot):
 A.note W V d p q= hopF (0:Site N) A.death W.birth (A.endTag p).2 (W.startTag q).2 (Kea.tax d) 1 V R:=by
 have ht:signW (A.endTag p).2=true:= A.lowerF p d N; have hp:signW (W.startTag q).2=false:= W.upperF q d N; unfold note upperT lowerT personA endTag startTag; rw [Emu.cat]; simp only [show signW ⟨_,p,1⟩=true from ht,show signW ⟨_,q,1⟩=false from hp, Bool.true_eq_false,ite_true,ite_false]
 positivity
end YM.CF.Buffered.Ballad.Lead
