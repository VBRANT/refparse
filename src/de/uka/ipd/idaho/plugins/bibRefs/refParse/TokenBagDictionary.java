/* RefParse, the algorithm for parsing lists of bibliographic references.
 * Copyright (C) 2011-2013 ViBRANT (FP7/2007-2013, GA 261532), by G. Sautter
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */
package de.uka.ipd.idaho.plugins.bibRefs.refParse;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map.Entry;
import java.util.Set;

import de.uka.ipd.idaho.gamta.Annotation;
import de.uka.ipd.idaho.gamta.AnnotationUtils;
import de.uka.ipd.idaho.gamta.Gamta;
import de.uka.ipd.idaho.gamta.TokenSequence;
import de.uka.ipd.idaho.gamta.Tokenizer;
import de.uka.ipd.idaho.stringUtils.Dictionary;
import de.uka.ipd.idaho.stringUtils.StringIterator;
import de.uka.ipd.idaho.stringUtils.StringVector;
import de.uka.ipd.idaho.stringUtils.regExUtils.RegExUtils;

/**
 * Fuzzy lookup dictionary intended for proper names. On lookup, this dictionary
 * considers capitalized tokens (and token parts, in case of camel case tokens)
 * of the string in question for determining a match. If specified in the
 * constructor, it abstracts from the actual order of the parts of a name. While
 * this may yield false positives in some cases, it is highly helpful with
 * person names, whose parts can be ordered in many different way.
 * 
 * TODO: consider moving this class to GAMTA main package
 * 
 * @author sautter
 */
public class TokenBagDictionary implements Dictionary {
	private static final boolean DEBUG = false;
	private static final boolean DEBUG_ABBREVIATION_MATCH = true;
	private static final boolean DEBUG_BAG_MATCH = false;
	
	private Tokenizer tokenizer = Gamta.INNER_PUNCTUATION_TOKENIZER;
	
//	/** complete entries (for quick lookup) */
//	private Set entries = new HashSet();
	/**  lower case parts allowed in lookups */
	private Set lowerCaseTokens = new HashSet() {
		public boolean contains(Object o) {
			if ((o instanceof String) && (((String) o).length() == 1) && (Gamta.LOWER_CASE_LETTERS.indexOf(((String) o).charAt(0)) != -1))
				return true;
			return super.contains(o);
		}
	};
//	/** normalized entries (concatenation of capitalized tokens in lexicographical or original order, depending on order sensitivity) */
//	private Set tokenBagEntries = new HashSet();
	/** complete entries (for quick lookup) */
	private HashMap entries = new HashMap();
//	/**  lower case parts allowed in lookups */
//	private HashMap lowerCaseTokens = new HashMap();
	/** normalized entries (concatenation of capitalized tokens in lexicographical or original order, depending on order sensitivity) */
	private HashMap tokenBagEntries = new HashMap();
	
	/** single tokens of all entries, for providing all proper start tokens */
	private Set stringTokens = new HashSet();
	/** mapping of the token bag keys of the entries to the respective token sets */
	private HashMap stringTokenBagSets = new HashMap();
	
	private boolean orderSensitive = false;
	private String reorderPunctuationMarks = null;
	
	private int maxEntryTokens = 0;
	private int maxMissingTokens = 0;
	private Dictionary externalLowerCaseTokens = null; // additional lower case parts for specifying allowed in lookups
	
//	private Set knownContainedEntries = new HashSet(); // cache for entries known to be contained (for quick lookup)
	private HashMap knownContainedEntries = new HashMap(); // cache for entries known to be contained (for quick lookup)
//	private Set knownNonContainedEntries = new HashSet(); // cache for entries known to be not contained (for quick lookup)
	private HashMap knownNonContainedEntries = new LinkedHashMap(1024, 0.9f, true) { // cache for entries known to be not contained (for quick lookup)
		protected boolean removeEldestEntry(Entry eldest) {
			return (this.size() > 4096);
		}
	};
	
	
	/** Constructor
	 */
	public TokenBagDictionary() {}
	
	/** Constructor
	 * @param orderSensitive observe order on lookups?
	 */
	public TokenBagDictionary(boolean orderSensitive) {
		this.orderSensitive = orderSensitive;
	}
	
	/** Constructor
	 * @param reorderPunctuationMarks a string of punctuation marks at which to break order sensitivity
	 */
	public TokenBagDictionary(String reorderPunctuationMarks) {
		this.orderSensitive = (reorderPunctuationMarks != null);
		this.reorderPunctuationMarks = reorderPunctuationMarks;
	}
	
	/** Constructor
	 * @param tokenizer the tokenizer to use
	 * @param orderSensitive observe order on lookups?
	 */
	public TokenBagDictionary(Tokenizer tokenizer) {
		this.tokenizer = tokenizer;
	}
	
	/** Constructor
	 * @param tokenizer the tokenizer to use
	 * @param orderSensitive observe order on lookups?
	 */
	public TokenBagDictionary(Tokenizer tokenizer, boolean orderSensitive) {
		this.tokenizer = tokenizer;
		this.orderSensitive = orderSensitive;
	}
	
	/** Constructor
	 * @param tokenizer the tokenizer to use
	 * @param reorderPunctuationMarks a string of punctuation marks at which to break order sensitivity
	 */
	public TokenBagDictionary(Tokenizer tokenizer, String reorderPunctuationMarks) {
		this.tokenizer = tokenizer;
		this.orderSensitive = (reorderPunctuationMarks != null);
		this.reorderPunctuationMarks = reorderPunctuationMarks;
	}
	
	/**
	 * Add an entry to the dictionary.
	 * @param entry the string to add
	 */
	public void addEntry(String entry) {
		
		//	TODO add 'dirty' flag to avoid writing unmodified dictionary
		
		if (DEBUG) System.out.println("Adding " + entry);
		
		if (this.reorderPunctuationMarks != null) {
			entry = reorderAtPunctuationMarks(entry, this.reorderPunctuationMarks);
			if (DEBUG) System.out.println(" broken to " + entry);
		}
		
		StringDataSet sd = getStringDataSet(entry, this.tokenizer, this.orderSensitive);
		
//		this.entries.add(sd.string);
		this.entries.put(sd.string, sd);
		this.stringTokens.addAll(Arrays.asList(sd.stringTokens));
		this.lowerCaseTokens.addAll(sd.lowerCaseTokens);
		
		this.maxEntryTokens = Math.max(this.maxEntryTokens, sd.stringTokens.length);
		
		ArrayList stringTokenBagSet = ((ArrayList) this.stringTokenBagSets.get(sd.tokenBagKey));
		if (stringTokenBagSet == null) {
			stringTokenBagSet = new ArrayList(2);
			this.stringTokenBagSets.put(sd.tokenBagKey, stringTokenBagSet);
		}
		stringTokenBagSet.add(sd);
		
		//	add token bags leaving out any one initial, allowing for sub sets of token bags to be found
		for (int s = 0; s < sd.tokenBagKey.length(); s++) {
			String tokenBagKey = (sd.tokenBagKey.substring(0, s) + sd.tokenBagKey.substring(s+1));
			stringTokenBagSet = ((ArrayList) this.stringTokenBagSets.get(tokenBagKey));
			if (stringTokenBagSet == null) {
				stringTokenBagSet = new ArrayList(2);
				this.stringTokenBagSets.put(tokenBagKey, stringTokenBagSet);
			}
			stringTokenBagSet.add(sd);
		}
		
//		this.tokenBagEntries.add(sd.tokenBagString);
		this.tokenBagEntries.put(sd.tokenBagString, sd);
		
		this.knownNonContainedEntries.clear();
	}
	
	/**
	 * @return the number of tokens of the dictionary's longest entry
	 */
	public int getMaxEntryTokens() {
		return this.maxEntryTokens;
	}
	
	/**
	 * Retrieve the maximum number of tokens that may be missing in a lookup
	 * token bag in comparison to a reference token bag in order for a match to
	 * succeed.
	 * @return the maximum number of missing tokens in a token bag match
	 */
	public int getMaxMissingTokens() {
		return this.maxMissingTokens;
	}
	
	/**
	 * Specify a dictionary containing lower case tokens allowed in lookups.
	 * Specifying null will disallow all lower case tokens not added through
	 * some string via the addEntry() method.
	 * @param externalLowerCaseTokens a dictionary containing lower case tokens
	 *            allowed in lookups
	 */
	private void setExternalLowerCaseTokens(Dictionary externalLowerCaseTokens) {
		if (externalLowerCaseTokens != this.lowerCaseTokens) {
			if (this.lowerCaseTokens == null)
				this.knownNonContainedEntries.clear();
			else if (externalLowerCaseTokens == null)
				this.knownContainedEntries.clear();
			else {
				this.knownNonContainedEntries.clear();
				this.knownContainedEntries.clear();
			}
		}
		this.externalLowerCaseTokens = externalLowerCaseTokens;
	}
	
	/**
	 * Set the maximum number of tokens that may be missing in a lookup token
	 * bag in comparison to a reference token bag in order for a match to
	 * succeed. A lower number will result in more accurate lookup, a higher
	 * number in more tolerance regarding missing tokens.
	 * @param maxMissingTokens the maximum number of missing tokens in a token
	 *            bag match.
	 */
	public void setMaxMissingTokens(int maxMissingTokens) {
		if (maxMissingTokens < this.maxMissingTokens)
			this.knownContainedEntries.clear();
		else if (this.maxMissingTokens < maxMissingTokens)
			this.knownNonContainedEntries.clear();
		this.maxMissingTokens = Math.max(maxMissingTokens, 0);
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.stringUtils.Dictionary#isDefaultCaseSensitive()
	 */
	public boolean isDefaultCaseSensitive() {
		return true;
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.stringUtils.Dictionary#lookup(java.lang.String, boolean)
	 */
	public boolean lookup(String string, boolean caseSensitive) {
		return this.lookup(string);
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.stringUtils.Dictionary#lookup(java.lang.String)
	 */
	public boolean lookup(String string) {
		if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("Looking up: " + string);
		if (this.knownContainedEntries.containsKey(string))
			return true;
		else if (this.knownNonContainedEntries.containsKey(string))
			return false;
		int match = this.doLookup(string);
		if (match != NOT_MATCHED)
			this.knownContainedEntries.put(string, new Integer(match));
		else this.knownNonContainedEntries.put(string, "");
		if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  ==> " + translate(match));
		return (match != NOT_MATCHED);
//		if (this.knownContainedEntries.containsKey(string))
//			return true;
//		else if (this.knownNonContainedEntries.contains(string))
//			return false;
//		StringDataSet sd = this.doLookup(string);
//		if (sd != null)
//			this.knownContainedEntries.put(string, sd);
//		else this.knownNonContainedEntries.add(string);
//		if (DEBUG) System.out.println("  ==> " + (sd != null));
//		return (sd != null);
//		if (this.knownContainedEntries.contains(string))
//			return true;
//		else if (this.knownNonContainedEntries.contains(string))
//			return false;
//		boolean contained = this.doLookup(string);
//		if (contained)
//			this.knownContainedEntries.add(string);
//		else this.knownNonContainedEntries.add(string);
//		if (DEBUG) System.out.println("  ==> " + contained);
//		return contained;
	}
	
	private static String translate(int match) {
		if (match == NOT_MATCHED)
			return "No Match";
		if (match == EQUAL_MATCH)
			return "Full Match";
		StringBuffer sb = new StringBuffer("Match");
		if ((match & ALL_TOKENS_MATCHED) != 0)
			sb.append(", no omissions");
		if ((match & NO_TOKENS_ABBREVIATED) != 0)
			sb.append(", no abbreviations");
		if ((match & LOWER_CASE_TOKENS_MATCHED) != 0)
			sb.append(", no lower case omissions");
		if ((match & TOKEN_ORDER_MATCHED) != 0)
			sb.append(", no reorderings");
		return sb.toString();
	}
	
	private static final int NOT_MATCHED = 0; // not a match
	private static final int EQUAL_MATCH = 255; // full equals() match
	private static final int MATCHED = 1; // some sort of match
	private static final int ALL_TOKENS_MATCHED = 2; // all capitalized tokens matched
	private static final int NO_TOKENS_ABBREVIATED = 4; // all capitalized tokens matched without abbreviation
	private static final int LOWER_CASE_TOKENS_MATCHED = 8; // all lower tokens matched to single entry as well
	private static final int TOKEN_ORDER_MATCHED = 16; // all (matched) tokens matched in original order
	
	private int doLookup(String string) {
		if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("Looking up: " + string);
		if (this.reorderPunctuationMarks != null) {
			string = reorderAtPunctuationMarks(string, this.reorderPunctuationMarks);
			if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println(" broken to " + string);
		}
		
		//	look up cache for positives
		if (this.knownContainedEntries.containsKey(string)) {
			if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - known positive: " + string);
			return ((Integer) this.knownContainedEntries.get(string)).intValue();
		}
		
		//	look up cache for negatives
		if (this.knownNonContainedEntries.containsKey(string)) {
			if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - known negative: " + string);
			return NOT_MATCHED;
		}
		
		//	look up string as a whole
		if (this.entries.containsKey(string)) {
			if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - known entry: " + string);
			return EQUAL_MATCH;
		}
		
		//	get data set only now (saves trashing cache with negatives)
		StringDataSet sd = getStringDataSet(string, this.tokenizer, this.orderSensitive);
		
		//	check lower case tokens (ignore ones that have only a single letter)
		if (!this.lowerCaseTokens.containsAll(sd.lowerCaseTokens)) {
			if (this.externalLowerCaseTokens == null)
				return NOT_MATCHED;
			else for (Iterator lit = sd.lowerCaseTokens.iterator(); lit.hasNext();) {
				String lowerCaseToken = ((String) lit.next());
				if ((lowerCaseToken.length() > 1) && !this.lowerCaseTokens.contains(lowerCaseToken) && !this.externalLowerCaseTokens.lookup(lowerCaseToken))
					return NOT_MATCHED;
			}
		}
		
		//	look up normalized string (helps with alternate orderings, e.g. in person names, or omitted internal stop words)
		if (this.tokenBagEntries.containsKey(sd.tokenBagString)) {
			if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - known token bag: " + string);
			StringDataSet lsd = ((StringDataSet) this.tokenBagEntries.get(sd.tokenBagString));
			int match = (MATCHED | ALL_TOKENS_MATCHED | NO_TOKENS_ABBREVIATED);
			if (this.orderSensitive)
				match = (match | TOKEN_ORDER_MATCHED);
			if (lsd.lowerCaseTokens.containsAll(sd.lowerCaseTokens))
				match = (match | LOWER_CASE_TOKENS_MATCHED);
			return match;
		}
		
		//	look up token bags (helps with abbreviated parts)
		ArrayList stringTokenBagSet = ((ArrayList) this.stringTokenBagSets.get(sd.tokenBagKey));
		if (stringTokenBagSet != null) {
			StringDataSet msd = null;
			for (Iterator sdit = stringTokenBagSet.iterator(); sdit.hasNext();) {
				StringDataSet lsd = ((StringDataSet) sdit.next());
				if ((sd.stringTokens.length == 1) && (lsd.stringTokens.length != 1))
					continue; // don't look up single word against word pairs
				boolean matched;
				if (this.orderSensitive)
					matched = (isAbbreviationOf(sd.tokenBagString, lsd.tokenBagString) || ((sd.stringTokens.length > 1) && isAbbreviationOf(lsd.tokenBagString, sd.tokenBagString)));
				else matched = bagEquals(sd.tokenBag, lsd.tokenBag, this.maxMissingTokens);
				if (matched) {
					if (lsd.lowerCaseTokens.containsAll(sd.lowerCaseTokens)) {
						int match = (MATCHED | ALL_TOKENS_MATCHED | LOWER_CASE_TOKENS_MATCHED);
						if (this.orderSensitive)
							match = (match | TOKEN_ORDER_MATCHED);
						if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - direct matched against " + lsd.string);
						return match;
					}
					else msd = lsd;
				}
			}
			if (msd != null) {
				int match = (MATCHED | ALL_TOKENS_MATCHED);
				if (this.orderSensitive)
					match = (match | TOKEN_ORDER_MATCHED);
				if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - matched against " + msd.string);
				return match;
			}
		}
		
		//	look for possibly matching token bag sets with difference larger than 1 (they are not indexed)
		if (this.maxMissingTokens > 1) {
			for (Iterator tbkit = this.stringTokenBagSets.keySet().iterator(); tbkit.hasNext();) {
				String tokenBagKey = ((String) tbkit.next());
				if (Math.abs(tokenBagKey.length() - sd.tokenBagKey.length()) <= this.maxMissingTokens)
					continue;
				if (isAbbreviationOf(sd.tokenBagKey, tokenBagKey)) {
					StringDataSet msd = null;
					for (Iterator sdit = stringTokenBagSet.iterator(); sdit.hasNext();) {
						StringDataSet lsd = ((StringDataSet) sdit.next());
						boolean matched;
						if (this.orderSensitive)
							matched = (isAbbreviationOf(sd.tokenBagString, lsd.tokenBagString) || ((sd.stringTokens.length > 1) && isAbbreviationOf(lsd.tokenBagString, sd.tokenBagString)));
						else matched = bagEquals(sd.tokenBag, lsd.tokenBag, this.maxMissingTokens);
						if (matched) {
							if (lsd.lowerCaseTokens.containsAll(sd.lowerCaseTokens)) {
								int match = (MATCHED | LOWER_CASE_TOKENS_MATCHED);
								if (this.orderSensitive)
									match = (match | TOKEN_ORDER_MATCHED);
								if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - direct sparse matched against " + lsd.string);
								return match;
							}
							else msd = lsd;
						}
					}
					if (msd != null) {
						int match = MATCHED;
						if (this.orderSensitive)
							match = (match | TOKEN_ORDER_MATCHED);
						if (DEBUG && (this.orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("  - sparse matched against " + msd.string);
						return match;
					}
				}
			}
		}
		
		//	nothing helped ...
		return NOT_MATCHED;
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.stringUtils.Dictionary#isEmpty()
	 */
	public boolean isEmpty() {
		return (this.size() == 0);
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.stringUtils.Dictionary#size()
	 */
	public int size() {
		return this.stringTokens.size();
	}

	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.stringUtils.Dictionary#getEntryIterator()
	 */
	public StringIterator getEntryIterator() {
		final Iterator it = this.stringTokens.iterator();
		return new StringIterator() {
			public boolean hasMoreStrings() {
				return this.hasNext();
			}
			public String nextString() {
				return ((String) this.next());
			}
			public boolean hasNext() {
				return it.hasNext();
			}
			public Object next() {
				return it.next();
			}
			public void remove() {
				it.remove();
			}
		};
	}
	
	/**
	 * @return an iterator over the entries that have explicitly been added to
	 *         the dictionary
	 */
	public StringIterator getStringEntryIterator() {
		final Iterator it = this.entries.keySet().iterator();
		return new StringIterator() {
			public boolean hasMoreStrings() {
				return this.hasNext();
			}
			public String nextString() {
				return ((String) this.next());
			}
			public boolean hasNext() {
				return it.hasNext();
			}
			public Object next() {
				return it.next();
			}
			public void remove() {
				it.remove();
			}
		};
	}
	
	private static class StringDataSet {
		/** the string the set is created from */
		final String string;
		/** the first letter up tokens in their original order */
		final String[] stringTokens;
		
		/** the upper case letters of the string in original or lexicographical order, depending on order sensitivity */
		final String tokenBagKey;
		/** all parts of the original string starting with a capital letter, broken up at internal capital letters, in original or lexicographical order, depending on order sensitivity */
		final String[] tokenBag;
		/** all parts of the original string that start with a capital letter concatenated with separating spaces, broken up at internal capital letters, in original or lexicographical order, depending on order sensitivity */
		final String tokenBagString;
		
		/** the lower case tokens contained in the original string */
		final Set lowerCaseTokens;
		
		StringDataSet(String string, String[] stringTokens, String stringTokenBagKey, String[] stringTokenBag, String stringTokenBagString, Set lowerCaseTokens) {
			this.string = string;
			this.stringTokens = stringTokens;
			this.tokenBagKey = stringTokenBagKey;
			this.tokenBag = stringTokenBag;
			this.tokenBagString = stringTokenBagString;
			this.lowerCaseTokens = lowerCaseTokens;
		}
	}
	
	private static HashMap stringDataSetCacheOI = new LinkedHashMap(1024, 0.9f, true) {
		protected boolean removeEldestEntry(Entry eldest) {
			return (this.size() > 2048);
		}
	};
	private static HashMap stringDataSetCacheOS = new LinkedHashMap(1024, 0.9f, true) {
		protected boolean removeEldestEntry(Entry eldest) {
			return (this.size() > 2048);
		}
	};
	private static HashMap getStringDataSetCache(boolean orderSensitive) {
		return (orderSensitive ? stringDataSetCacheOS : stringDataSetCacheOI);
	}
	private static StringDataSet getStringDataSet(String string, Tokenizer tokenizer, boolean orderSensitive) {
		
		//	do cache lookup (if cache active)
		HashMap stringDataSetCache = getStringDataSetCache(orderSensitive);
		StringDataSet sd = ((stringDataSetCache == null) ? null : ((StringDataSet) stringDataSetCache.get(string)));
		
		//	cahce hit, we're done
		if (sd != null) {
			if (DEBUG && (orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) System.out.println("TBD cache hit");
			return sd;
		}
		
		//	cache miss, parse string
		TokenSequence stringTokenSequence = tokenizer.tokenize(Gamta.normalize(string));
		
		StringVector stringTokens = new StringVector();
		StringVector stringSubTokenInitials = new StringVector();
		StringVector stringSubTokens = new StringVector();
		
		Set lowerCaseTokens = new HashSet();
		
		for (int t = 0; t < stringTokenSequence.size(); t++) {
			String stringToken = stringTokenSequence.valueAt(t);
			char ch = stringToken.charAt(0);
			if (('A' <= ch) && (ch <= 'Z')) {
				stringTokens.addElement(stringToken);
				
				//	upper case only at start, store complete token
				if (Gamta.isCapitalizedWord(stringToken)) {
					stringSubTokenInitials.addElement("" + ch);
					stringSubTokens.addElement(stringToken);
				}
				
				//	more than one upper case letter, cut token apart
				else {
					StringBuffer subToken = new StringBuffer();
					for (int c = 0; c < stringToken.length(); c++) {
						ch = stringToken.charAt(c);
						if (('A' <= ch) && (ch <= 'Z')) {
							if (subToken.length() != 0) {
								stringSubTokens.addElement(subToken.toString());
								subToken = new StringBuffer();
							}
							stringSubTokenInitials.addElement("" + ch);
						}
						subToken.append(ch);
					}
					if (subToken.length() != 0)
						stringSubTokens.addElement(subToken.toString());
				}
			}
			
			else if (('0' <= ch) && (ch <= '9')) {
				stringTokens.addElement(stringToken);
				
				//	extract digit blocks
				StringBuffer subToken = new StringBuffer();
				for (int c = 0; c < stringToken.length(); c++) {
					ch = stringToken.charAt(c);
					if (('0' <= ch) && (ch <= '9')) {
						subToken.append(ch);
					}
					else if (subToken.length() != 0) {
						stringSubTokens.addElement(subToken.toString());
						stringSubTokenInitials.addElement("" + subToken.charAt(0));
						subToken = new StringBuffer();
					}
				}
				if (subToken.length() != 0) {
					stringSubTokens.addElement(subToken.toString());
					stringSubTokenInitials.addElement("" + subToken.charAt(0));
				}
			}
			
			else if (('a' <= ch) && (ch <= 'z'))
				lowerCaseTokens.add(stringToken);
		}
		
		if (!orderSensitive) {
			stringSubTokenInitials.sortLexicographically();
			stringSubTokens.sortLexicographically();
		}
		
		if (DEBUG && (orderSensitive ? DEBUG_ABBREVIATION_MATCH : DEBUG_BAG_MATCH)) {
			System.out.println("SubTokenInitials: " + stringSubTokenInitials.concatStrings(" - "));
			System.out.println("SubTokens: " + stringSubTokens.concatStrings(" - "));
			System.out.println("LowerCase: " + lowerCaseTokens);
		}
		
		sd = new StringDataSet(string, stringTokens.toStringArray(), stringSubTokenInitials.concatStrings(""), stringSubTokens.toStringArray(), stringSubTokens.concatStrings(" "), lowerCaseTokens);
		if (stringDataSetCache != null) stringDataSetCache.put(string, sd);
		
		//	down here, we got the data either way
		return sd;
	}
	
	private static boolean bagEquals(String[] test, String[] reference, int maxMissingTokens) {
		if (DEBUG && DEBUG_BAG_MATCH) {
			System.out.print("Test:");
			for (int t = 0; t < test.length; t++)
				System.out.print(" " + test[t]);
			System.out.println();
			System.out.print("Reference:");
			for (int r = 0; r < reference.length; r++)
				System.out.print(" " + reference[r]);
			System.out.println();
		}
		
		//	consider maximum length difference between test and reference arrays
		if (Math.abs(test.length - reference.length) > maxMissingTokens)
			return false;
		
		//	clone arrays in order not to destroy argument data structures
		test = clone(test);
		reference = clone(reference);
		
		//	test all tokens individually
		int maxMatchLength = 0;
		boolean testIsAbbreviated = false;
		boolean referenceIsAbbreviated = false;
		for (int t = 0; t < test.length; t++) {
			
			//	find best match in reference token bag
			int bestMatchLength = 0;
			int bestMatchLengthDifference = Integer.MAX_VALUE;
			int bestMatchIndex = -1;
			for (int r = 0; r < reference.length; r++) {
				if (reference[r] == null)
					continue;
				if ((test[t].charAt(0) != reference[r].charAt(0)))
					continue;
				if (!isAbbreviationOf(test[t], reference[r]) && !isAbbreviationOf(reference[r], test[t]))
					continue;
				int matchLength = Math.min(test[t].length(), reference[r].length());
				int matchLengthDifference = Math.abs(test[t].length() - reference[r].length());
				if ((matchLength > bestMatchLength) || ((matchLength == bestMatchLength) && (matchLengthDifference < bestMatchLengthDifference))) {
					bestMatchLength = matchLength;
					bestMatchLengthDifference = Math.abs(test[t].length() - reference[r].length());
					bestMatchIndex = r;
				}
			}
			
			//	could not match this one
			if (bestMatchIndex == -1) return false;
			
			//	sort out matched up reference token
			if (DEBUG && DEBUG_BAG_MATCH) System.out.println("Matched " + test[t] + " to " + reference[bestMatchIndex]);
			if (test[t].length() < reference[bestMatchIndex].length())
				testIsAbbreviated = true;
			if (test[t].length() > reference[bestMatchIndex].length())
				referenceIsAbbreviated = true;
			maxMatchLength = Math.max(maxMatchLength, bestMatchLength);
			reference[bestMatchIndex] = null;
		}
		
		//	if parts of both test and reference have been matched as abbreviations, we need some additional safety
		if (DEBUG && DEBUG_BAG_MATCH) System.out.println(" ==> " + ((maxMatchLength > ((testIsAbbreviated && referenceIsAbbreviated) ? 3 : 1)) ? "" : "no ") + "match");
		return (maxMatchLength > ((testIsAbbreviated && referenceIsAbbreviated) ? 3 : 1));
	}
	
	private static String[] clone(String[] source) {
		String[] clone = new String[source.length];
		System.arraycopy(source, 0, clone, 0, source.length);
		return clone;
	}
	
	private static boolean isAbbreviationOf(String abbreviation, String full) {
		if (DEBUG && DEBUG_ABBREVIATION_MATCH) System.out.println("Abbreviation matching " + abbreviation + " against " + full);
		
		//	abbreviation longer than full form ==> abbreviation match impossible
		if (full.length() < abbreviation.length()) {
			if (DEBUG && DEBUG_ABBREVIATION_MATCH) System.out.println(" ==> full too short");
			return false;
		}
		
		//	remove dots
		full = removeDots(full);
		abbreviation = removeDots(abbreviation);
		
		//	abbreviation longer than full form ==> abbreviation match impossible
		if (full.length() < abbreviation.length()) {
			if (DEBUG && DEBUG_ABBREVIATION_MATCH) System.out.println(" ==> de-dotted full too short");
			return false;
		}
		
		//	check letter by letter
		int a = 0;
		for (int f = 0; f < full.length(); f++) {
			
			//	we've reached the end of the abbreviation, so it fits
			if (a == abbreviation.length()) {
				if (DEBUG && DEBUG_ABBREVIATION_MATCH) System.out.println(" ==> prefix match");
				return true;
			}
			
			//	get next character of full form
			char fch = full.charAt(f);
			
			//	check next character of abbreviation
			char ach = abbreviation.charAt(a);
			
			//	letters match, continue to next one
			if (ach == fch) {
				a++;
				continue;
			}
			
			//	jump over internal high commas (may mark omission in abbreviations like "Intern'l")
			if (ach == '\'') {
				a++;
				if (a == abbreviation.length()) {
					if (DEBUG && DEBUG_ABBREVIATION_MATCH) System.out.println(" ==> prefix match");
					return true;
				}
				ach = abbreviation.charAt(a);
			}
			
			//	letters match, proceed to next one 
			if (ach == fch)
				a++;
			
			//	break and fail if next letter in abbreviation is non-space and not a word start and next letter in full form is space
			if ((fch == ' ') && (ach != ' ') && (a != 0) && (abbreviation.charAt(a-1) != ' ')) {
				if (DEBUG && DEBUG_ABBREVIATION_MATCH) System.out.println(" ==> no match for incomplete token coverage");
				return false;
			}
			
			//	otherwise, consider current letter of full form as omitted
		}
		
		//	we have a match if we have reached the end of the abbreviation
		if (DEBUG && DEBUG_ABBREVIATION_MATCH) System.out.println(" ==> " + ((a == abbreviation.length()) ? "full match" : "no match for incomplete coverage"));
		return (a == abbreviation.length());
	}
	
	private static String removeDots(String str) {
		StringBuffer dotFreeStr = new StringBuffer();
		for (int c = 0; c < str.length(); c++) {
			char ch = str.charAt(c);
			if (ch != '.')
				dotFreeStr.append(ch);
		}
		return dotFreeStr.toString();
	}
	
	private static String reorderAtPunctuationMarks(String str, String punctuationMarks) {
		String[] strParts = str.split("\\s*[" + RegExUtils.escapeForRegEx(punctuationMarks) + "]\\s*");
		if (strParts.length < 2)
			return str;
		Arrays.sort(strParts);
		StringBuffer reorderedStr = new StringBuffer();
		for (int p = 0; p < strParts.length; p++) {
			if (p != 0)
				reorderedStr.append(' ');
			reorderedStr.append(strParts[p]);
		}
		return reorderedStr.toString();
	}
	
	/**
	 * Create annotations marking all parts of a token sequence that are
	 * contained in this token bag dictionary. This method loops through to its
	 * static variant and is provided for convenience.
	 * @param tokens the token sequence to annotate
	 * @param allowOverlap allow overlapping results?
	 * @param lowerCaseTokens a dictionary containing lower case tokens allowed
	 *        to be included in matches, in addition to the ones that by
	 *        ways of entries belong to this token bag dictionary (specifying
	 *        null allows no extra lower case tokens)
	 * @return an array holding annotations marking all parts of a token
	 *         sequence that are contained in this token bag dictionary
	 */
	public Annotation[] extractAllContained(TokenSequence tokens, boolean allowOverlap, Dictionary lowerCaseTokens) {
		return extractAllContained(tokens, this, allowOverlap, lowerCaseTokens);
	}
	
	/**
	 * Create annotations marking all parts of a token sequence that are
	 * contained in a token bag dictionary. This method uses
	 * Gamta.extractAllContained() internally, but does some parameter
	 * computations specific to token sequence dictionaries.
	 * @param tokens the token sequence to annotate
	 * @param tbd the token bag dictionary to do the lookups in
	 * @param allowOverlap allow overlapping results?
	 * @param lowerCaseTokens a dictionary containing lower case tokens allowed
	 *        to be included in matches, in addition to the ones that by
	 *        ways of entries belong to the specified token bag dictionary
	 *        (specifying null allows no extra lower case tokens)
	 * @return an array holding annotations marking all parts of a token
	 *         sequence that are contained in a token bag dictionary
	 */
	public static Annotation[] extractAllContained(TokenSequence tokens, TokenBagDictionary tbd, boolean allowOverlap, Dictionary lowerCaseTokens) {
		
		//	allow extra lower case tokens
		tbd.setExternalLowerCaseTokens(lowerCaseTokens);
		
		//	extract annotations
		Annotation[] preResult = Gamta.extractAllContained(tokens, tbd, (tbd.getMaxEntryTokens() * 3), true, true, false);
		
		//	truncate leading and tailing non-capitalized tokens
		for (int r = 0; r < preResult.length; r++) {
			
			//	check quality of match (lookup goes to cache anyways)
			int match = tbd.doLookup(preResult[r].getValue());
			if (match == EQUAL_MATCH) {
				preResult[r].setAttribute("matchedWholeString", "true");
				continue;
			}
			
			//	match detail attributes
			if ((match & ALL_TOKENS_MATCHED) != 0)
				preResult[r].setAttribute("matchedAllTokens", "true");
			if ((match & NO_TOKENS_ABBREVIATED) != 0)
				preResult[r].setAttribute("matchedFullTokens", "true");
			if ((match & LOWER_CASE_TOKENS_MATCHED) != 0)
				preResult[r].setAttribute("matchedLowerCase", "true");
			if ((match & TOKEN_ORDER_MATCHED) != 0)
				preResult[r].setAttribute("matchedTokenOrder", "true");
			
			//	retain leading and tailing lower case tokens?
			boolean retainLowerCaseLeadAndTail = ((match & LOWER_CASE_TOKENS_MATCHED) != 0);
			
			//	truncate tokens
			int start = preResult[r].getStartIndex();
			int end = preResult[r].getEndIndex();
			while (start < end) {
				if (Gamta.isFirstLetterUpWord(tokens.valueAt(start)))
					break;
				if (tokens.valueAt(start).matches("[a-z]++\\'[A-Z][a-zA-Z]*+"))
					break;
				if (Gamta.isNumber(tokens.valueAt(start)))
					break;
				if (retainLowerCaseLeadAndTail && Gamta.isWord(tokens.valueAt(start)))
					break;
				start++;
			}
			while (end > start) {
				if (Gamta.isFirstLetterUpWord(tokens.valueAt(end-1)))
					break;
				if (tokens.valueAt(end-1).matches("[a-z]++\\'[A-Z][a-zA-Z]*+"))
					break;
				if (Gamta.isNumber(tokens.valueAt(end-1)))
					break;
				if (retainLowerCaseLeadAndTail && Gamta.isWord(tokens.valueAt(end-1)))
					break;
				end--;
			}
			
			//	scan for brackets that remain open
			String openBracket = null;
			for (int t = start; t < end; t++) {
				if (Gamta.isOpeningBracket(tokens.valueAt(t)))
					openBracket = tokens.valueAt(t);
				else if ((openBracket != null) && Gamta.closes(tokens.valueAt(t), openBracket))
					openBracket = null;
			}
			while ((openBracket != null) && (end < preResult[r].getEndIndex()) && !Gamta.closes(tokens.valueAt(end-1), openBracket))
				end++;
			
			//	do modifications (if any)
			if ((end - start) < preResult[r].size())
				preResult[r] = Gamta.newAnnotation(tokens, preResult[r].getType(), start, (end - start));
		}
		
		//	sort out duplicates
		Set resultKeys = new HashSet();
		ArrayList resultList = new ArrayList();
		for (int r = 0; r < preResult.length; r++)
			if (resultKeys.add(preResult[r].getStartIndex() + "-" + preResult[r].getEndIndex()))
				resultList.add(preResult[r]);
		Collections.sort(resultList);
		
		//	sort out overlapping matches if required
		if (!allowOverlap) {
			for (int r = 1; r < resultList.size(); r++)
				if (AnnotationUtils.overlaps(((Annotation) resultList.get(r-1)), ((Annotation) resultList.get(r))))
					resultList.remove(r--);
		}
		
		//	return remainder
		return ((Annotation[]) resultList.toArray(new Annotation[resultList.size()]));
	}
	
	//	for test purposes only
	public static void main(String[] args) {
//		System.out.println(isAbbreviationOf("Verhandlung", "Verh"));
//		System.out.println(isAbbreviationOf("Zeitschrift", "Ztschr"));
//		System.out.println(isAbbreviationOf("Hamburg", "Hmbg"));
//		System.out.println(isAbbreviationOf("Mahrburg", "Hmbg"));
//		System.out.println(isAbbreviationOf("International", "Intn'l"));
//		System.out.println(isAbbreviationOf("Jour. Nat. Hist.", "J Nat Hist"));
//		System.out.println(isAbbreviationOf("Journal of Natural History", "J.Nat. Hist."));
//		System.out.println(isAbbreviationOf("Natural History Journal", "J. Nat. Hist."));
		
//		TokenBagDictionary pTbd = new TokenBagDictionary(":,");
//		pTbd.addEntry("Cambridge, MA: Harvard University Press");
//		System.out.println(pTbd.lookup("Cambridge, MA: Harv. Univ. Press"));
//		System.out.println(pTbd.lookup("Harvard Univ. Press, Cambridge, MA"));
//		pTbd.addEntry("Pyle, RL");
//		System.out.println(pTbd.lookup("Richard L. Pyle"));
		TokenBagDictionary aTbd = new TokenBagDictionary(false);
		aTbd.addEntry("Pyle, RL");
		System.out.println(aTbd.lookup("Richard L. Pyle"));
		
//		TokenBagDictionary tbd = new TokenBagDictionary();
////		tbd.addEntry("Fisher, Brian Lee");
//		tbd.setMaxMissingTokens(1);
////		test(tbd, "B. L. Fisher");
////		test(tbd, "BL Fisher");
////		test(tbd, "PL Fisher");
////		test(tbd, "B Fisher");
////		test(tbd, "Fisher BL");
//		
////		tbd.addEntry("Cambridge: Havard Univ. Press");
////		test(tbd, "Havard University Press, Cambridge");
////		test(tbd, "Havard University Press, Cambridge, MA");
////		test(tbd, "Havard University Press, Cambridge, Massachusetts");
//		
////		tbd.addEntry("Havard University Press, Cambridge, MA");
////		test(tbd, "Havard University Press, Cambridge");
////		test(tbd, "Havard University Press, Cambridge, MA");
////		tbd.setMaxMissingTokens(2);
////		test(tbd, "Havard University Press, Cambridge");
////		test(tbd, "Cambridge: Havard Univ. Press");
//		
////		tbd.addEntry("Transactions of the Linnean Society of London. Zoology (2)");
//		tbd.addEntry("Rozas J");
//		tbd.addEntry("Rozas R");
//		
////		TokenSequence ts = Gamta.INNER_PUNCTUATION_TOKENIZER.tokenize("Fisher BL (2005) A Model for a Global Inventory of Ants: A Case Study in Madagascar. In: Jablonski NG, ed. Proceedings of the California Academy of Sciences 56: 78-89.");
////		TokenSequence ts = Gamta.INNER_PUNCTUATION_TOKENIZER.tokenize("25. Forel A (1912) The Percy Sladen Trust Expedition to the Indian Ocean in 1905, under the leadership of Mr. J. Stanley Gardiner, M.A. Volume 4. No. XI. Fourmis des Seychelles et des Aldabras, recues de M. Hugh Scott. Transactions of the Linnean Society of London. Zoology (2)15: 159-167.");
//		TokenSequence ts = Gamta.INNER_PUNCTUATION_TOKENIZER.tokenize("Rozas J, Rozas R");
//		Annotation[] authors = extractAllContained(ts, tbd, false, null);
//		for (int a = 0; a < authors.length; a++)
//			System.out.println(authors[a]);
	}
	
	static void test(TokenBagDictionary tbd, String test) {
		System.out.println(tbd.getMaxMissingTokens() + " - " + test + ": " + tbd.lookup(test));
	}
}
