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

import java.awt.BorderLayout;
import java.awt.Color;
import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.Reader;
import java.io.Writer;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Date;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Properties;
import java.util.TreeMap;
import java.util.TreeSet;

import javax.swing.DefaultComboBoxModel;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JDialog;
import javax.swing.JPanel;

import de.uka.ipd.idaho.gamta.Annotation;
import de.uka.ipd.idaho.gamta.AnnotationUtils;
import de.uka.ipd.idaho.gamta.Gamta;
import de.uka.ipd.idaho.gamta.MutableAnnotation;
import de.uka.ipd.idaho.gamta.TokenSequence;
import de.uka.ipd.idaho.gamta.TokenSequenceUtils;
import de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer;
import de.uka.ipd.idaho.gamta.util.AnalyzerDataProvider;
import de.uka.ipd.idaho.gamta.util.AnnotationFilter;
import de.uka.ipd.idaho.gamta.util.AnnotationPatternMatcher;
import de.uka.ipd.idaho.gamta.util.AnnotationPatternMatcher.AnnotationIndex;
import de.uka.ipd.idaho.gamta.util.analyzerConfiguration.AnalyzerConfigPanel;
import de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel;
import de.uka.ipd.idaho.gamta.util.feedback.html.FeedbackPanelHtmlRenderer.FeedbackPanelHtmlRendererInstance;
import de.uka.ipd.idaho.gamta.util.feedback.html.renderers.AnnotationEditorFeedbackPanelRenderer;
import de.uka.ipd.idaho.gamta.util.feedback.html.renderers.BufferedLineWriter;
import de.uka.ipd.idaho.gamta.util.feedback.panels.AnnotationEditorFeedbackPanel;
import de.uka.ipd.idaho.plugins.bibRefs.BibRefConstants;
import de.uka.ipd.idaho.plugins.bibRefs.BibRefTypeSystem;
import de.uka.ipd.idaho.stringUtils.StringIndex;
import de.uka.ipd.idaho.stringUtils.StringIterator;
import de.uka.ipd.idaho.stringUtils.StringVector;
import de.uka.ipd.idaho.stringUtils.regExUtils.RegExUtils;

/**
 * Source-wise singleton data container and utility class for the RefParse
 * bibliographic reference parsing algorithm.
 * 
 * @author sautter
 */
public abstract class RefParse extends AbstractConfigurableAnalyzer implements BibRefConstants {
	
	/* TODO Use Style Templates in RefParse (and reference handling in general)
- author list style:
  - LF: "<lastName>',' <firstName>"
  - LI: "<lastName>','? <Initials>"
  - FL: "<firstName> <lastName>"
  - IL: "<Initials> <lastName>"
  - LF+FL: changing name part order
  - LI+IL: dito
- build author names from atoms and expansively using annotation patterns (like authority names in TreeFAT)
==> allows for injecting known last names even if they don't match patterns ("Ng" !!!) by means of annotating before calling RefParse
- author list separator(s)
- author names in all-caps?

- title/journal separator
- are journal/publisher names in italics?
- publisher part order:
  - LN: "<location> ':'? <name>"
  - NL: "<name> ',' <location>"

- reference numbering scheme (also for reference tagging):
  - "N": last name of first author
  - "P": parentheses
  - "Q": square brackets
  - "E": enumeration "<number> '.'?"
==> allow index letters in years only if style is "N"

- expect use of author repetition markers?

- reference start style:
  - outdented
  - indented
  - neither
==> even allows for correcting paragraph boundaries below "References" heading


- also observe numbering scheme in reference detection


- also observe numbering scheme in reference citation tagger (even though it should usually infer pretty safely)
	 */
	
	private static final String VOLUME_DESIGNATOR_TYPE = VOLUME_DESIGNATOR_ANNOTATION_TYPE;
	private static final String ISSUE_DESIGNATOR_TYPE = ISSUE_DESIGNATOR_ANNOTATION_TYPE;
	private static final String NUMBER_DESIGNATOR_TYPE = NUMERO_DESIGNATOR_ANNOTATION_TYPE;
	private static final String FASCICLE_DESIGNATOR_TYPE = "fascicle";
	private static final String SERIES_DESIGNATOR_TYPE = "series";
	
	public static final String GOT_FEEDBACK_ATTRIBUTE = "_gfb";
	private static final String NO_BIB_REF_ATTRIBUTE = "_nbr";
	
	private static final String AUTHOR_LIST_ANNOTATION_TYPE = "authorList";
	private static final String EDITOR_LIST_ANNOTATION_TYPE = "editorList";
	private static final String PAGE_RANGE_ANNOTATION_TYPE = "pageRange";
	private static final String NEXT_REFERENCE_ANNOTATION_TYPE = "nextRef";
	
	private static final String VOLUME_REFERENCE_ANNOTATION_TYPE = "volumeRef";
	private static final boolean integrateVolumeRefs = true;
	
	private static final boolean detailOrigin = false;
	
	private static final boolean DEBUG = true;
	
	private static final boolean DEBUG_STRUCTURE_SCORING = (DEBUG && true);
	
	private static final boolean DEBUG_AUTHOR_NAME_EXTRACTION = (DEBUG && false);
	private static final boolean DEBUG_AUTHOR_LIST_ASSEMBLY = (DEBUG && false);
	
	
	private HashMap highlightAttributeCache = new HashMap();
	private Color getAnnotationHighlight(String type) {
		Color color = ((Color) this.highlightAttributeCache.get(type));
		if (color == null) {
			if (AUTHOR_ANNOTATION_TYPE.equals(type))
				color = Color.ORANGE;
			else if (EDITOR_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.darken(Color.ORANGE);
			else if (TITLE_ANNOTATION_TYPE.equals(type))
				color = Color.GREEN;
			else if (VOLUME_TITLE_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.darken(Color.GREEN);
			else if (YEAR_ANNOTATION_TYPE.equals(type))
				color = Color.RED;
			else if (JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE.equals(type))
				color = Color.YELLOW;
			else if (JOURNAL_NAME_ANNOTATION_TYPE.equals(type))
				color = Color.CYAN;
			else if (PUBLISHER_ANNOTATION_TYPE.equals(type))
				color = Color.YELLOW;
			else if (LOCATION_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.darken(Color.YELLOW);
			else if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(type))
				color = Color.PINK;
			else if (NEXT_REFERENCE_ANNOTATION_TYPE.equals(type))
				color = Color.GRAY;
			else if (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(type))
				color = Color.BLUE;
			else if (PAGINATION_ANNOTATION_TYPE.equals(type) || PAGE_NUMBER_TYPE.equals(type) || PAGE_RANGE_ANNOTATION_TYPE.equals(type))
				color = Color.MAGENTA;
			else if (PUBLICATION_DOI_ANNOTATION_TYPE.equals(type))
				color = Color.LIGHT_GRAY;
			else if (PUBLICATION_URL_ANNOTATION_TYPE.equals(type))
				color = Color.LIGHT_GRAY;
			else if (BOOK_CONTENT_INFO_ANNOTATION_TYPE.equals(type))
				color = FeedbackPanel.brighten(Color.BLUE);
			else color = new Color(Color.HSBtoRGB(((float) Math.random()), 0.5f, 1.0f));
			this.highlightAttributeCache.put(type, color);
		}
		return color;
	}
	
	private String authorRepetitionMarkerRegEx = 
			"(" +
				"([\\-]+)" +
				"|" +
				"(Ders(\\.|elbe))" +
				"|" +
				"(Dies(\\.|(elben?)))" +
				"|" +
				"(Same(\\sas\\sabove)?)" +
			")";
	
	private String editorListTagBaseRegEx = 
			"(" +
				"(Ed(s|s\\.|\\.|itors|itor)?)" +
				"|" +
				"(Red(s|s\\.|\\.|acteurs|acteur)?)" +
				"|" +
				"(Hrsg\\.|Hg\\.)" +
			")";
	private String editorListTagRegEx = 
			"(" +
				"(\\(" + this.editorListTagBaseRegEx + "\\))" +
				"|" +
				"(\\[" + this.editorListTagBaseRegEx + "\\])" +
				"|" +
				"(" + this.editorListTagBaseRegEx + ")" +
			")";
	
	private String authorLastNameBaseRegEx = 
			"([A-Za-z]+\\'?)?" +
			"(" +
				"(" +
					"[A-Z]" +
					"(" +
						"([a-z\\-]*[aeiouy][a-z]*)" +
						"|" +
						"([A-Z]*[AEIOUY][A-Z]*)" +
						"|" +
						"([a-z]{1,2})" +
					")" +
				")" +
				"|" +
				"(" +
					"[AEIOUY]" +
					"(" +
						"([a-z\\-]*[a-z]+)" +
						"|" +
						"[A-Z]+" +
					")" +
				")" +
			")" +
			"(\\'[a-z]+)?";
	private String authorLastNameRegEx = "(" + this.authorLastNameBaseRegEx + ")((\\-|\\s)?" + this.authorLastNameBaseRegEx + ")*";
	
	private String authorFirstNameBaseRegEx = 
			"(" +
				"[A-Z]" +
				"(" +
					"([a-z\\-]*[aeiouy][a-z]*)" +
					"|" +
					"([A-Z]*[AEIOUY][A-Z]*)" +
				")" +
			")" +
			"|" +
			"(" +
				"[AEIOUY]" +
				"(" +
					"[a-z\\-]+" +
					"|" +
					"[A-Z]+" +
				")" +
			")";
	private String authorFirstNameRegEx = "(" + this.authorFirstNameBaseRegEx + ")((\\-|\\s)?" + this.authorFirstNameBaseRegEx + ")*";
	
	private String authorInitialsBaseRegEx = 
		"[A-Z]" +
		"(" +
			"\\." +
		")?";
	private String authorInitialsRegEx = "(" + this.authorInitialsBaseRegEx + ")(((\\s?\\-\\s?)|\\s)?" + this.authorInitialsBaseRegEx + ")*";
	
	private String authorNameAffixRegEx = 
		"(" +
			"\\,?\\s*" +
			"(" +
				"Jr" +
				"|" +
				"Sr" +
				"|" +
				"(" +
					"X{0,3}" +
					"(" +
						"I{1,4}" +
						"|" +
						"IV" +
						"|" +
						"(VI{0,4})" +
						"|" +
						"IX" +
					")" +
				")" +
				"|" +
				"(1\\s?st)" +
				"|" +
				"(2\\s?nd)" +
				"|" +
				"(3\\s?rd)" +
				"|" +
				"([4-9]\\s?th)" +
			")" +
			"\\.?" +
		")";
	
	private String nobleTitleNameRegEx = "([A-Z][a-z]{3,}\\s)+(of|the|(of\\sthe)|de|(de\\sla)|von|van|(von\\sder)|(van\\sder)|vom|(von\\sden)|(von\\sdem)|(van\\sde))+(\\s[A-Z][a-z]{3,})+";
	
	private StringVector nobleTitleStarts = new StringVector();
	
	private StringVector authorNameStopWords = new StringVector();
	
	private StringVector authorListSeparators = new StringVector();
	
	private TokenBagDictionary knownAuthors = new TokenBagDictionary();
	
	private StringVector knownNonAuthorNames = new StringVector();
	
	private StringVector knownNonAuthorNameStarts = new StringVector();
	
	
	private String yearRegEx = "((1[5-9])|20)[0-9]{2}";//"[12][0-9]{3}";
	
	
	private String pageRegEx = 
			"(" +
				"(p\\.|page)" +
				"\\s" +
			")?" +
			"[1-9][0-9]{0,5}";
	
	private String pageRangeArabicRegEx = 
			"(" +
				"(pp\\.|pages)" +
				"\\s" +
			")?" +
			"[1-9][0-9]{0,5}\\s*[\\-\\u2012-\\u2015]\\s*[1-9][0-9]{0,5}";
	private String romanNumberRegEx = "((c?m+)?(c?d)?(x?c+)?(x?l)?(i?x+)?(i?v)?(i+)?)";
	private String pageRangeRomanRegEx = 
			"(" +
				"(pp\\.|pages)" +
				"\\s" +
			")?" +
			this.romanNumberRegEx +
			"\\s*[\\-\\u2012-\\u2015]\\s*" +
			this.romanNumberRegEx;
	
	
	private String partDesignatorRegEx = "(([1-9][0-9]*+)|([Ii]?[Xx]*[Vv]?[Ii]*)|([A-Z]))";
	
	
	private StringVector numberingInvalidatorsLeading = new StringVector();
	private StringVector numberingInvalidatorsTailing = new StringVector();
	private StringVector bookContentHintNumberingInvalidatorsTailing = new StringVector();
	private StringVector titleNumberPatterns = new StringVector();
	
	private StringVector volumeDesignatorHints = new StringVector();
	private StringVector issueDesignatorHints = new StringVector();
	private StringVector numberDesignatorHints = new StringVector();
	private StringVector fascicleDesignatorHints = new StringVector();
	private StringVector seriesDesignatorHints = new StringVector();
	private StringVector partDesignatorHints = new StringVector();
	
	private StringVector partDesignatorBlockSeparators = new StringVector();
	
	private String titleCaseAbbreviationRegEx = 
		"(" +
			"(" +
				"[A-Z]" +
				"[a-z]*" +
				"(\\.?\\-)" +
			")*" +
			"(" +
				"[A-Z]" +
				"(" +
					"[a-z]*" +
					"[a-df-z]" + // abbreviations almost never end with an 'e'
				")?" +
				"\\." +
			")" +
			"(" +
				"\\-" +
				"[A-Za-z]" +
				"[a-z]*" +
				"\\." +
			")*" +
		")" +
		"|" +
		"([1-9][0-9]*)";
	private String titleCaseAbbreviationBlockRegEx = ("" +
			"(" + this.titleCaseAbbreviationRegEx + ")" +
			"(" +
				"\\s*" +
				"([a-z]{1,4}\\.?\\s)*" +
				"(" + this.titleCaseAbbreviationRegEx + ")" +
			")+" +
			"");
	
	private String titleCaseTokenRegEx = 
			"(" +
				"(" +
					"((d|l)\\')?" +
					"[A-Z]" +
					"(" +
						"([a-z]{0,3}\\.\\s\\-\\s)" +
						"|" + // catch Gamta's normalization (will add spaces around dash if preceeded by dot)
						"(([A-Z]+|[a-z]+)?\\-)" +
					")" +
				")*" +
				"(" +
					"((d|l)\\')?" +
					"[A-Z]" +
					"(" +
						"[A-Z]+" +
						"|" +
						"([a-z]{0,3}\\.)" +
						"|" +
						"[a-z]+" +
					")" +
				")" +
			")" +
			"|" +
			"([1-9][0-9]*)" +
			"";
	
	private StringVector titleCaseBlockStopWords = Gamta.getNoiseWords();
	
	private StringVector knownTitleCaseBlockPatterns = new StringVector();
	
	private StringVector countryNames = new StringVector();
	
	private StringVector conferenceSynonyms = new StringVector();
	
	private StringVector titleCaseAbbreviations = new StringVector();
	
	private TokenBagDictionary knownJournalsAndPublishers = new TokenBagDictionary(true);
	private StringVector journalPublisherStopWords = new StringVector();
	
	private WordUseStat jopWordStat = new WordUseStat();
	
	private static final String urlChar = "[a-zA-Z0-9\\-\\_\\!\\~\\*\\'\\(\\)]";
	private static final String urlPattern = 
			"(https|http|ftp)\\:\\/\\/" +
			"" + urlChar + "+(\\." + urlChar + "+)+(:[0-9]++)?" +
			"(\\/" + urlChar + "+(\\." + urlChar + "+)*)*" +
			"(\\?.*)?";
	private static final String doiPattern =
				"(" +
					"http\\:\\/\\/dx\\.doi\\.org\\/" +
					"|" +
					"(doi\\:\\s?)" +
				")?" +
				"10\\.[0-9]++\\/[^\\s]++";
	
	
	private StringVector relevantTypes = new StringVector();
	private StringVector transferableTypes = new StringVector();
	
	private TreeMap referenceTypes = new TreeMap();
	
	private BibRefTypeSystem referenceTypeSystem = null;
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#initAnalyzer()
	 */
	public void initAnalyzer() {
		
		//	read stop words for title case blocks
		this.titleCaseBlockStopWords.clear();
		this.titleCaseBlockStopWords.addContentIgnoreDuplicates(this.readList("titleCaseBlockStopWords"));
		
		//	read journal/publisher tokens
		this.jopWordStat = new WordUseStat();
		try {
			BufferedReader jwsBr = new BufferedReader(new InputStreamReader(this.dataProvider.getInputStream("knownJopWords.txt"), "UTF-8"));
			this.jopWordStat.readData(jwsBr);
			jwsBr.close();
		} catch (IOException fnfe) {}
		
		//	read stop words for author names
		this.authorNameStopWords.clear();
		this.authorNameStopWords.addContentIgnoreDuplicates(this.readList("authorNameStopWords"));
		
		//	read author list separators
		this.authorListSeparators.clear();
		this.authorListSeparators.addContentIgnoreDuplicates(this.readList("authorListSeparators"));
		
		
		//	read base regular expression patterns and assemble main patterns
		this.authorLastNameBaseRegEx = this.readRegEx("authorLastNameBase", this.authorLastNameBaseRegEx);
		this.authorLastNameRegEx = "(" + this.authorLastNameBaseRegEx + ")((\\-|\\s)?" + this.authorLastNameBaseRegEx + ")*";
		
		this.authorFirstNameBaseRegEx = this.readRegEx("authorFirstNameBase", this.authorFirstNameBaseRegEx);
		this.authorFirstNameRegEx = "(" + this.authorFirstNameBaseRegEx + ")((\\-|\\s)?" + this.authorFirstNameBaseRegEx + ")*";
		
		this.authorInitialsBaseRegEx = this.readRegEx("authorInitialsBase", this.authorInitialsBaseRegEx);
		this.authorInitialsRegEx = "(" + this.authorInitialsBaseRegEx + ")(((\\s?\\-\\s?)|\\s)?" + this.authorInitialsBaseRegEx + ")*";
		
		this.authorNameAffixRegEx = this.readRegEx("authorNameAffix", this.authorInitialsBaseRegEx);
		
		this.nobleTitleNameRegEx = this.readRegEx("nobleTitleName", this.nobleTitleNameRegEx);
		this.nobleTitleStarts.addContentIgnoreDuplicates(this.readList("nobleTitleStarts"));
		
		this.authorRepetitionMarkerRegEx = this.readRegEx("authorRepetitionMarker", this.authorRepetitionMarkerRegEx);
		
		this.editorListTagBaseRegEx = this.readRegEx("editorListTagBase", this.editorListTagBaseRegEx);
		this.editorListTagRegEx = 
				"(" +
					"(\\(" + this.editorListTagBaseRegEx + "\\))" +
					"|" +
					"(\\[" + this.editorListTagBaseRegEx + "\\])" +
					"|" +
					"(\\,?" + this.editorListTagBaseRegEx + ")" +
				")";
		
		this.knownNonAuthorNames.addContentIgnoreDuplicates(this.readList("knownNonAuthorNames"));
		this.knownNonAuthorNameStarts.addContentIgnoreDuplicates(this.readList("knownNonAuthorNameStarts"));
		
		
		this.pageRegEx = this.readRegEx("page", this.pageRegEx);
		this.pageRangeArabicRegEx = this.readRegEx("pageRangeArabic", this.pageRangeArabicRegEx);
		this.pageRangeRomanRegEx = this.readRegEx("pageRangeRoman", this.pageRangeRomanRegEx);
		
		this.numberingInvalidatorsLeading.clear();
		this.numberingInvalidatorsLeading.addContentIgnoreDuplicates(this.readList("numberingInvalidatorsLeading"));
		
		this.numberingInvalidatorsTailing.clear();
		this.numberingInvalidatorsTailing.addContentIgnoreDuplicates(this.readList("numberingInvalidatorsTailing"));
		
		this.bookContentHintNumberingInvalidatorsTailing.clear();
		this.bookContentHintNumberingInvalidatorsTailing.addContentIgnoreDuplicates(this.readList("bookContentInfoNumberingInvalidatorsTailing"));
		
		this.numberingInvalidatorsTailing.addContentIgnoreDuplicates(this.bookContentHintNumberingInvalidatorsTailing);
		
		this.titleNumberPatterns.clear();
		this.titleNumberPatterns.addContentIgnoreDuplicates(this.readList("titleNumberPatterns"));
		
		this.partDesignatorRegEx = this.readRegEx("partDesignator", this.partDesignatorRegEx);
		
		this.volumeDesignatorHints.parseAndAddElements("v.;vol.;volume;Band;Bd.;Heft", ";");
		this.issueDesignatorHints.parseAndAddElements("i.;issue", ";");
		this.numberDesignatorHints.parseAndAddElements("n.;nr;nr.;no;no.;number", ";");
		this.fascicleDesignatorHints.parseAndAddElements("f.;fasc.;fascicle", ";");
		this.seriesDesignatorHints.parseAndAddElements("s.;ser.;series", ";");
		this.seriesDesignatorHints.parseAndAddElements("sect.;section", ";");
		
		this.partDesignatorHints.addContentIgnoreDuplicates(this.volumeDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.issueDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.numberDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.fascicleDesignatorHints);
		this.partDesignatorHints.addContentIgnoreDuplicates(this.seriesDesignatorHints);
		
		this.partDesignatorBlockSeparators.parseAndAddElements("(;);,", ";");
		
		this.titleCaseAbbreviationRegEx = this.readRegEx("titleCaseAbbreviation", this.titleCaseAbbreviationRegEx);
		this.titleCaseAbbreviationBlockRegEx = ("" +
				"(" + this.titleCaseAbbreviationRegEx + ")" +
				"(" +
					"\\s*" +
					"([a-z]{1,4}\\.?\\s)*" +
					"(" + this.titleCaseAbbreviationRegEx + ")" +
				")+" +
				"");
		
		this.titleCaseTokenRegEx = this.readRegEx("titleCaseToken", this.titleCaseTokenRegEx);
		
		//	read title case abbreviations and countries
		this.titleCaseAbbreviations.clear();
		this.titleCaseAbbreviations.addContentIgnoreDuplicates(this.readList("titleCaseAbbreviations"));
		
		this.countryNames.clear();
		this.countryNames.addContentIgnoreDuplicates(this.readList("countries"));
		
		this.conferenceSynonyms.clear();
		this.conferenceSynonyms.addContentIgnoreDuplicates(this.readList("conferenceSynonyms"));
		
		this.knownTitleCaseBlockPatterns.clear();
		this.knownTitleCaseBlockPatterns.addContentIgnoreDuplicates(this.readList("knownTitleCaseBlockPatterns"));
		for (int c = 0; c < this.conferenceSynonyms.size(); c++) {
			String cs = this.conferenceSynonyms.get(c);
			if (cs.endsWith("."))
				this.titleCaseAbbreviations.addElementIgnoreDuplicates(cs);
			this.knownTitleCaseBlockPatterns.addElement("Proceedings.*" + RegExUtils.escapeForRegEx(cs));
			this.knownTitleCaseBlockPatterns.addElement("Proc\\..*" + RegExUtils.escapeForRegEx(cs));
		}
		
		//	read data types & colors
		try {
			InputStream is = this.dataProvider.getInputStream("relevantTypes.txt");
			StringVector typeLines = StringVector.loadList(is);
			is.close();
			
			this.relevantTypes.clear();
			
			for (int t = 0; t < typeLines.size(); t++) {
				String typeLine = typeLines.get(t).trim();
				if ((typeLine.length() != 0) && !typeLine.startsWith("//")) {
					int split = typeLine.indexOf(' ');
					if (split == -1)
						this.relevantTypes.addElement(typeLine);
					else {
						String type = typeLine.substring(0, split).trim();
						Color color = FeedbackPanel.getColor(typeLine.substring(split).trim());
						this.relevantTypes.addElement(type);
						this.highlightAttributeCache.put(type, color);
					}
				}
			}
		} catch (IOException fnfe) {}
		
		//	add fix types
		this.relevantTypes.addElementIgnoreDuplicates(AUTHOR_ANNOTATION_TYPE);
		if (integrateVolumeRefs)
			this.relevantTypes.addElementIgnoreDuplicates(EDITOR_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(YEAR_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(TITLE_ANNOTATION_TYPE);
		if (detailOrigin) {
			this.relevantTypes.addElementIgnoreDuplicates(VOLUME_TITLE_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(JOURNAL_NAME_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(PUBLISHER_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(LOCATION_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		}
		else {
			this.relevantTypes.removeAll(VOLUME_TITLE_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(JOURNAL_NAME_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(PUBLISHER_ANNOTATION_TYPE);
			this.relevantTypes.removeAll(LOCATION_ANNOTATION_TYPE);
			this.relevantTypes.addElementIgnoreDuplicates(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		}
		if (integrateVolumeRefs)
			this.relevantTypes.addElementIgnoreDuplicates(VOLUME_TITLE_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PAGINATION_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PART_DESIGNATOR_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PUBLICATION_DOI_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(PUBLICATION_URL_ANNOTATION_TYPE);
		this.relevantTypes.addElementIgnoreDuplicates(BOOK_CONTENT_INFO_ANNOTATION_TYPE);
		
		//	add transferable types TODO check out if transfer is sensible (causes errors if element not given in subsequent references)
		this.transferableTypes.addElementIgnoreDuplicates(AUTHOR_ANNOTATION_TYPE);
		this.transferableTypes.addElementIgnoreDuplicates(YEAR_ANNOTATION_TYPE);
		this.transferableTypes.addElementIgnoreDuplicates(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		
		//	add available reference types TODO load descriptors of reference types from BibRefTypeSystem
		this.referenceTypes.clear();
		this.referenceTypes.put(JOURNAL_ARTICEL_REFERENCE_TYPE, new BibRefType(JOURNAL_ARTICEL_REFERENCE_TYPE, "Journal Article"));
		this.referenceTypes.put(JOURNAL_VOLUME_REFERENCE_TYPE, new BibRefType(JOURNAL_VOLUME_REFERENCE_TYPE, "Journal Volume"));
		this.referenceTypes.put(BOOK_REFERENCE_TYPE, new BibRefType(BOOK_REFERENCE_TYPE, "Book / Thesis / Monograph"));
		this.referenceTypes.put(BOOK_CHAPTER_REFERENCE_TYPE, new BibRefType(BOOK_CHAPTER_REFERENCE_TYPE, "Book Chapter"));
		this.referenceTypes.put(PROCEEDINGS_REFERENCE_TYPE, new BibRefType(PROCEEDINGS_REFERENCE_TYPE, "Conference Proceedings"));
		this.referenceTypes.put(PROCEEDINGS_PAPER_REFERENCE_TYPE, new BibRefType(PROCEEDINGS_PAPER_REFERENCE_TYPE, "Proceedings Paper"));
		this.referenceTypes.put(URL_REFERENCE_TYPE, new BibRefType(URL_REFERENCE_TYPE, "Online Document / Website / etc."));
		
		this.referenceTypeSystem = BibRefTypeSystem.getInstance(this.dataProvider, "RefClassifierTypeSystem.xml", false);
//		BibRefTypeSystem.BibRefType[] brts = this.referenceTypeSystem.getBibRefTypes();
//		for (int t = 0; t < brts.length; t++) {
//			if (!brts[t].name.startsWith("book"))
//				brts[t].addCondition(GPathParser.parseExpression("./@bookContentInfo"), "Only books have content hints.");
//		}
		
		//	load learned authors
		try {
			InputStream is = this.dataProvider.getInputStream("knownAuthors.txt");
			StringVector knownAuthors = StringVector.loadList(new InputStreamReader(is, "UTF-8"));
			is.close();
			
			this.knownAuthors = new TokenBagDictionary();
			
			for (int a = 0; a < knownAuthors.size(); a++)
				this.knownAuthors.addEntry(knownAuthors.get(a));
		}
		catch (IOException fnfe) {
			fnfe.printStackTrace(System.out);
		}
		
		//	load learned journal names and publishers
		try {
			InputStream is = this.dataProvider.getInputStream("knownJournalsAndPublishers.txt");
			StringVector knownJournalsAndPublishers = StringVector.loadList(new InputStreamReader(is, "UTF-8"));
			is.close();
			
			this.knownJournalsAndPublishers = new TokenBagDictionary(true);
			
			for (int a = 0; a < knownJournalsAndPublishers.size(); a++)
				this.knownJournalsAndPublishers.addEntry(knownJournalsAndPublishers.get(a));
		}
		catch (IOException fnfe) {
			fnfe.printStackTrace(System.out);
		}
		
		//	stop words for recognition
		this.journalPublisherStopWords.clear();
		this.journalPublisherStopWords.addContentIgnoreDuplicates(this.readList("journalPublisherStopWords"));
	}
	
	private String[] readList(String name) {
		StringVector list = new StringVector();
		
		try {
			InputStream is = this.dataProvider.getInputStream(name + ".list.txt");
			StringVector loadList = StringVector.loadList(new InputStreamReader(is, "UTF-8"));
			is.close();
			
			for (int t = 0; t < loadList.size(); t++) {
				String listEntry = loadList.get(t).trim();
				if ((listEntry.length() != 0) && !listEntry.startsWith("//"))
					list.addElement(listEntry);
			}
		}
		catch (IOException ioe) {
			System.out.println("Exception loading list '" + name + "': " + ioe.getMessage());
		}
		
		return list.toStringArray();
	}
	
	private String readRegEx(String name, String def) {
		try {
			InputStream is = this.dataProvider.getInputStream(name + ".regEx.txt");
			StringVector regEx = StringVector.loadList(new InputStreamReader(is, "UTF-8"));
			is.close();
			return RegExUtils.normalizeRegEx(regEx.concatStrings("\n"));
		}
		catch (IOException ioe) {
			System.out.println("Exception loading pattern '" + name + "': " + ioe.getMessage());
			return def;
		}
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#exitAnalyzer()
	 */
	public void exitAnalyzer() {
		
		//	store learned authors
		if (this.dataProvider.isDataEditable("knownAuthors.txt")) try {
			StringVector knownAuthors = new StringVector();
			for (StringIterator sit = this.knownAuthors.getStringEntryIterator(); sit.hasMoreStrings();)
				knownAuthors.addElementIgnoreDuplicates(sit.nextString());
			knownAuthors.sortLexicographically();
			
			OutputStream os = this.dataProvider.getOutputStream("knownAuthors.txt");
			knownAuthors.storeContent(new OutputStreamWriter(os, "UTF-8"));
			os.flush();
			os.close();
		} catch (IOException fnfe) {}
		
		//	store learned journal names and publishers
		if (this.dataProvider.isDataEditable("knownJournalsAndPublishers.txt")) try {
			StringVector knownJournalsAndPublishers = new StringVector();
			for (StringIterator sit = this.knownJournalsAndPublishers.getStringEntryIterator(); sit.hasMoreStrings();)
				knownJournalsAndPublishers.addElementIgnoreDuplicates(sit.nextString());
			knownJournalsAndPublishers.sortLexicographically();
			
			OutputStream os = this.dataProvider.getOutputStream("knownJournalsAndPublishers.txt");
			knownJournalsAndPublishers.storeContent(new OutputStreamWriter(os, "UTF-8"));
			os.flush();
			os.close();
		} catch (IOException fnfe) {}
		
		//	store learned journal/publisher tokens
		if (this.dataProvider.isDataEditable("knownJopWords.txt") && this.jopWordStat.isDirty()) try {
			BufferedWriter jwsBw = new BufferedWriter(new OutputStreamWriter(this.dataProvider.getOutputStream("knownJopWords.txt"), "UTF-8"));
			this.jopWordStat.writeData(jwsBw);
			jwsBw.close();
		} catch (IOException fnfe) {}
	}
	
	//	TODO use Analyzer Config API for egular expression patterns, with fixed names, forbidding to delete any of the built-in patterns
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#getConfigTitle()
	 */
	protected String getConfigTitle() {
		return "Configure RefParse";
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#customizeConfigDialog(javax.swing.JDialog)
	 */
	protected void customizeConfigDialog(JDialog dialog) {
		//	TODO use analyzer config API
		super.customizeConfigDialog(dialog);
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#getConfigPanels(javax.swing.JDialog)
	 */
	protected AnalyzerConfigPanel[] getConfigPanels(JDialog dialog) {
		//	TODO use analyzer config API
		return super.getConfigPanels(dialog);
	}
	
	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.AbstractConfigurableAnalyzer#configureProcessor()
	 */
	public void configureProcessor() {
		
		//	store current data so it appears in config dialogs
		this.exitAnalyzer();
		
		//	configure processor
		super.configureProcessor();
		
		//	put changes in effect
		this.initAnalyzer();
	}

	/* (non-Javadoc)
	 * @see de.uka.ipd.idaho.gamta.util.Analyzer#process(de.uka.ipd.idaho.gamta.MutableAnnotation, java.util.Properties)
	 */
	public void process(MutableAnnotation data, Properties parameters) {}
	
	AuthorListStyle parseBibRefs(MutableAnnotation data, MutableAnnotation[] bibRefAnnots, Properties parameters, AuthorListStyle authorListStyle) {
		
		//	check arguments
		if (bibRefAnnots.length == 0)
			return authorListStyle;
		
		//	filter out leading reference numbers
		int[] refNums = new int[bibRefAnnots.length];
		int refNumIndex = -1;
		int refStartIndex = 0;
		MutableAnnotation[] fullBibRefAnnots = null;
		for (int n = 0; n < 2; n++) {
			Arrays.fill(refNums, -1);
			boolean allRefNums = true;
			for (int r = 0; r < bibRefAnnots.length; r++) {
				if (bibRefAnnots[r].size() <= n) {
					allRefNums = false;
					break;
				}
				if (bibRefAnnots[r].valueAt(n).matches("[1-9][0-9]*"))
					refNums[r] = Integer.parseInt(bibRefAnnots[r].valueAt(n));
				else {
					allRefNums = false;
					break;
				}
			}
			if (!allRefNums)
				continue;
			for (int r = 1; r < bibRefAnnots.length; r++)
				if (refNums[r-1] != (refNums[r]-1)) {
					allRefNums = false;
					break;
				}
			if (!allRefNums)
				continue;
			refNumIndex = n;
		}
		
		//	found reference numbers, also get rid of associated punctuation
		if (refNumIndex != -1) {
			refStartIndex = refNumIndex+1;
			while ((refStartIndex < bibRefAnnots[0].size()) && Gamta.isPunctuation(bibRefAnnots[0].valueAt(refStartIndex))) {
				boolean punctuationMatch = true;
				for (int r = 1; r < bibRefAnnots.length; r++) {
					if (bibRefAnnots[r].size() <= refStartIndex) {
						punctuationMatch = false;
						break;
					}
					if (!bibRefAnnots[r].valueAt(refStartIndex).equals(bibRefAnnots[0].valueAt(refStartIndex))) {
						punctuationMatch = false;
						break;
					}
				}
				if (punctuationMatch)
					refStartIndex++;
				else break;
			}
			fullBibRefAnnots = new MutableAnnotation[bibRefAnnots.length];
		}
		
		//	cut reference numbers
		if (refStartIndex != 0)
			for (int r = 0; r < bibRefAnnots.length; r++) {
				fullBibRefAnnots[r] = bibRefAnnots[r];
				bibRefAnnots[r] = bibRefAnnots[r].addAnnotation(fullBibRefAnnots[r].getType(), refStartIndex, (fullBibRefAnnots[r].size() - refStartIndex));
				bibRefAnnots[r].copyAttributes(fullBibRefAnnots[r]);
			}
		
		//	initialize data structures
		BibRef[] bibRefs = new BibRef[bibRefAnnots.length];
		
		//	initialize data containers
		for (int r = 0; r < bibRefAnnots.length; r++)
			bibRefs[r] = new BibRef(bibRefAnnots[r]);
		
		//	do parsing
		AuthorListStyle als = this.parseBibRefs(bibRefs, authorListStyle);
		
		//	un-cut reference numbers
		if (refStartIndex != 0)
			for (int r = 0; r < bibRefAnnots.length; r++) {
				fullBibRefAnnots[r].copyAttributes(bibRefAnnots[r]);
				fullBibRefAnnots[r].removeAnnotation(bibRefAnnots[r]);
				bibRefAnnots[r] = fullBibRefAnnots[r];
			}
		
		//	finally ...
		return als;
	}
	
	AuthorListStyle parseBibRefs(BibRef[] bibRefs, AuthorListStyle authorListStyle) {
		
		//	initialize data containers and extract basic details (collect evidence on name form along the way)
		for (int r = 0; r < bibRefs.length; r++) {
			
			//	annotate URLs & DOIs (helps filtering numerical attributes)
			bibRefs[r].urls = Gamta.extractAllMatches(bibRefs[r].annotation, urlPattern, false, true, false);
			bibRefs[r].dois = Gamta.extractAllMatches(bibRefs[r].annotation, doiPattern, false, true, false);
			if (DEBUG && ((bibRefs[r].urls.length + bibRefs[r].dois.length) != 0)) {
				System.out.println("Found URLs/DOIs in " + bibRefs[r].annotation.getValue());
				for (int u = 0; u < bibRefs[r].urls.length; u++)
					System.out.println("  URL: " + bibRefs[r].urls[u].getValue());
				for (int d = 0; d < bibRefs[r].dois.length; d++)
					System.out.println("  DOI: " + bibRefs[r].dois[d].getValue());
			}
			
			//	mark numbers in contextx like "VLDB-11", "VLDB '11", "of the 2011 Joint Conference", etc.
			this.markTitleNumbers(bibRefs[r]);
//			
//			//	mark base details if necessary
//			if (bibRefs[r].preExistingStructure)
//				continue;
			this.getBaseDetails(bibRefs[r]);
		}
		
		//	mark author lists
		for (int r = 0; r < bibRefs.length; r++) {
//			if (bibRefs[r].preExistingStructure)
//				continue;
			this.getAuthorLists(bibRefs[r]);
		}
		
		//	filter author lists based on style
		if (authorListStyle == null)
			authorListStyle = this.getAuthorListStyle(bibRefs);
		this.filterAuthorLists(bibRefs, authorListStyle);
		
		//	extract all possible detail structures (as "<element> <punctuation>? <element> <punctuation>? <element> ...") and use th one which fits for most references
		StringIndex structureCounts = new StringIndex();
		HashMap typeElementSets = new HashMap();
		HashMap summaryElementSets = new HashMap();
		HashMap punctSummaryElementSets = new HashMap();
		for (int r = 0; r < bibRefs.length; r++) {
			
			//	get structures
			this.getStructures(bibRefs[r]);
			
			//	set up auxiliary data structures
			StringVector typeStrings = new StringVector();
			StringVector summaryStrings = new StringVector();
			StringVector punctSummaryStrings = new StringVector();
			
			//	count structures
			if (DEBUG) System.out.println(bibRefs[r].annotation.toXML());
			for (int s = 0; s < bibRefs[r].structures.size(); s++) {
				Structure structure = ((Structure) bibRefs[r].structures.get(s));
				if (structure.detailTypes.contains(PAGE_NUMBER_TYPE) && structure.detailTypes.contains(PAGE_RANGE_ANNOTATION_TYPE)) {
					bibRefs[r].structures.remove(s--);
					continue;
				}
				
				typeStrings.addElementIgnoreDuplicates(structure.typeString);
				if (!typeElementSets.containsKey(structure.typeString))
					typeElementSets.put(structure.typeString, new LinkedHashSet(Arrays.asList(structure.types)));
				
				summaryStrings.addElementIgnoreDuplicates(structure.summaryString);
				if (!summaryElementSets.containsKey(structure.summaryString))
					summaryElementSets.put(structure.summaryString, new LinkedHashSet(Arrays.asList(structure.summary)));
				
				punctSummaryStrings.addElementIgnoreDuplicates(structure.punctSummaryString);
				if (!punctSummaryElementSets.containsKey(structure.punctSummaryString))
					punctSummaryElementSets.put(structure.punctSummaryString, new LinkedHashSet(Arrays.asList(structure.punctSummary)));
			}
			
			for (int s = 0; s < typeStrings.size(); s++)
				structureCounts.add(typeStrings.get(s));
			for (int s = 0; s < summaryStrings.size(); s++)
				structureCounts.add(summaryStrings.get(s));
			for (int s = 0; s < punctSummaryStrings.size(); s++)
				structureCounts.add(punctSummaryStrings.get(s));
		}
		
		
		//	select best structure for each bibliographic reference, using global context
		StringVector separators = new StringVector();
		StringIndex separatorFrequencies = new StringIndex();
		for (int r = 0; r < bibRefs.length; r++) {
//			if (bibRefs[r].preExistingStructure)
//				continue;
			this.selectStructure(bibRefs[r], bibRefs.length, structureCounts, separators, separatorFrequencies, punctSummaryElementSets, summaryElementSets, typeElementSets);
		}
		
		//	extract primary separator char
		if (DEBUG) System.out.println("Got " + separators.size() + " separators from " + bibRefs.length + " bibliographic references:");
		String primarySeparator = "";
		int primarySeparatorFrequency = 0;
		for (int s = 0; s < separators.size(); s++) {
			String separator = separators.get(s);
			int separatorFrequency = separatorFrequencies.getCount(separator);
			if (!Gamta.isBracket(separator) && (primarySeparatorFrequency < separatorFrequency)) {
				primarySeparator = separator;
				primarySeparatorFrequency = separatorFrequency;
			}
			if (DEBUG) System.out.println("  - " + separator + " (" + separatorFrequency + ")");
		}
		if (DEBUG) {
			System.out.println("  ==> primary separator: " + primarySeparator);
			System.out.println();
		}
		
		//	identify volume references
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].preExistingStructure)
				continue;
			this.extractVolumeReference(bibRefs[r], primarySeparator, authorListStyle);
		}
		
		//	have to recurse even before getting title and origin, so to handle references whose origin lies outside an embedded volume reference
		if (integrateVolumeRefs && !VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRefs[0].annotation.getType()))
//			this.processVolumeRefs(data, bibRefs, authorListStyle, parameters);
			this.processVolumeRefs(bibRefs, authorListStyle);
		
		//	now that we're doing title, volume title, and journal/publisher together, we don't need to handle volume references any further
		if (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRefs[0].annotation.getType()))
			return authorListStyle;
		
		//	get all unassigned word blocks, and count intermediate punctuation blocks in ones with exactly two blocks
		StringVector tJopSeparators = new StringVector();
		StringIndex tJopSeparatorFrequencies = new StringIndex();
		for (int r = 0; r < bibRefs.length; r++) {
			this.getWordBlocks(bibRefs[r]);
			if (DEBUG) {
				System.out.println("Word blocks:");
				for (int b = 0; b < bibRefs[r].wordBlocks.length; b++)
					System.out.println(" - " + bibRefs[r].wordBlocks[b].getValue());
			}
			
			if (bibRefs[r].wordBlocks.length != 2)
				continue;
			boolean elementsBetween = false;
			for (int t = bibRefs[r].wordBlocks[0].getEndIndex(); t < bibRefs[r].wordBlocks[1].getStartIndex(); t++)
				if (bibRefs[r].wordBlockExcluded[t] || Gamta.isWord(bibRefs[r].annotation.valueAt(t)) || Gamta.isNumber(bibRefs[r].annotation.valueAt(t))) {
					elementsBetween = true;
					break;
				}
//				if (!"_".equals(bibRefs[r].structure.details[t]) || Gamta.isWord(bibRefs[r].annotation.valueAt(t)) || Gamta.isNumber(bibRefs[r].annotation.valueAt(t))) {
//					elementsBetween = true;
//					break;
//				}
			if (elementsBetween)
				continue;
			String tJopSeparator = TokenSequenceUtils.concatTokens(bibRefs[r].annotation, bibRefs[r].wordBlocks[0].getEndIndex(), (bibRefs[r].wordBlocks[1].getStartIndex() - bibRefs[r].wordBlocks[0].getEndIndex()));
			tJopSeparators.addElementIgnoreDuplicates(tJopSeparator);
			tJopSeparatorFrequencies.add(tJopSeparator);
		}
		
		//	find most frequent after-title separator
		if (DEBUG) System.out.println("Got " + tJopSeparators.size() + " after-title separators from " + bibRefs.length + " bibliographic references:");
		String tJopSeparator = "";
		TokenSequence tJopSeparatorTokens = null;
		int tJopSeparatorFrequency = 0;
		for (int s = 0; s < tJopSeparators.size(); s++) {
			String tJopSep = tJopSeparators.get(s);
			int tJopSepFrequency = tJopSeparatorFrequencies.getCount(tJopSep);
			if (tJopSeparatorFrequency < tJopSepFrequency) {
				tJopSeparator = tJopSep;
				tJopSeparatorFrequency = tJopSepFrequency;
			}
			if (DEBUG) System.out.println("  - " + tJopSep + " (" + tJopSepFrequency + ")");
		}
		if ((tJopSeparatorFrequency * 5) < bibRefs.length) {
			tJopSeparator = "";
			if (DEBUG) {
				System.out.println("  ==> primary after-title separator not found, support too low");
				System.out.println();
			}
		}
		else if (DEBUG) {
			tJopSeparatorTokens = Gamta.newTokenSequence(tJopSeparator, bibRefs[0].annotation.getTokenizer());
			System.out.println("  ==> primary after-title separator: " + tJopSeparator);
			System.out.println();
		}
		
		//	classify word blocks as title, volume title, and journal/publisher
//		for (int r = 0; r < bibRefs.length; r++) {
		for (int rt = 0; rt < bibRefs.length; rt++) {
			final int r = rt;
			if (bibRefs[r].preExistingStructure)
				continue;
			if (bibRefs[r].wordBlocks.length == 0)
				continue;
			
			//	rule: one block ==> title TODO for references without punctuation, try and find tailing title case block in title if no URL given (better than no journal/publisher at all)
			if (bibRefs[r].wordBlocks.length == 1) {
				bibRefs[r].title = bibRefs[r].wordBlocks[0];
				bibRefs[r].title.changeTypeTo(TITLE_ANNOTATION_TYPE);
				continue;
			}
			
			//	rule: two blocks ==> title, journal/publisher
			if (bibRefs[r].wordBlocks.length == 2) {
				bibRefs[r].title = bibRefs[r].wordBlocks[0];
				bibRefs[r].title.changeTypeTo(TITLE_ANNOTATION_TYPE);
				bibRefs[r].journalOrPublisher = bibRefs[r].wordBlocks[1];
				bibRefs[r].journalOrPublisher.changeTypeTo(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
				continue;
			}
			
			//	get known journal names and publishers 
			Annotation[] knownJops = this.getKnownJops(bibRefs[r]);
			
			//	get proceedings titles
			Annotation[] proceedingsTitles = this.getProceedingsTitles(bibRefs[r]);
			
			//	assess where journal/publisher might be
			int minJournalStart = 0;
			int maxJournalEnd = bibRefs[r].annotation.size();
			int partDesCount = 0;
			int minPublisherStart = 0;
			int maxPublisherEnd = bibRefs[r].annotation.size();
			
			//	check book content hints
			if (bibRefs[r].bookContentInfos.size() != 0) {
				for (int h = 0; h < bibRefs[r].bookContentInfos.size(); h++)
					maxPublisherEnd = Math.min(maxPublisherEnd, ((Annotation) bibRefs[r].bookContentInfos.get(h)).getStartIndex());
			}
			
			//	check journal part designators
			else {
				if (bibRefs[r].volumeDesignator != null) {
					maxJournalEnd = Math.min(maxJournalEnd, bibRefs[r].volumeDesignator.getStartIndex());
					partDesCount++;
				}
				if (bibRefs[r].issueDesignator != null) {
					maxJournalEnd = Math.min(maxJournalEnd, bibRefs[r].issueDesignator.getStartIndex());
					partDesCount++;
				}
				if (bibRefs[r].numberDesignator != null) {
					maxJournalEnd = Math.min(maxJournalEnd, bibRefs[r].numberDesignator.getStartIndex());
					partDesCount++;
				}
				
				//	if secure (range) pagination present and part designator far from pagination, use pagination as limit (catches un-recognized title numbers mistaken for part designators)
				if ((partDesCount != 0) && (bibRefs[r].pagination != null) && (bibRefs[r].pagination.size() > 1) && (maxJournalEnd < (bibRefs[r].pagination.getStartIndex() - (4 * partDesCount)))) {
					maxJournalEnd = bibRefs[r].pagination.getStartIndex();
					partDesCount = 0;
				}
			}
			
			//	score word blocks
			float[] wordBlockScores = new float[bibRefs[r].wordBlocks.length];
			float wordBlockScoreSum = 0;
			if (DEBUG) System.out.println("Scoring word blocks:");
			for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
				wordBlockScores[b] = this.getJopScore(bibRefs[r].wordBlocks[b]);
				if (DEBUG) System.out.println(" - " + bibRefs[r].wordBlocks[b].getValue() + " ==> " + wordBlockScores[b]);
				wordBlockScoreSum += wordBlockScores[b];
			}
			
			//	smooth scores
			if (DEBUG) System.out.println("Smoothing word block scores:");
			for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
				if (wordBlockScores[b] == 0)
					wordBlockScores[b] = (wordBlockScoreSum / (2 * bibRefs[r].wordBlocks.length));
				if (DEBUG) System.out.println(" - " + bibRefs[r].wordBlocks[b].getValue() + " ==> " + wordBlockScores[b]);
			}
			
			//	mark which word blocks can be merged and which cannot
			boolean[] canMergeWithSuccessor = new boolean[bibRefs[r].wordBlocks.length];
			Arrays.fill(canMergeWithSuccessor, true);
			if (DEBUG) System.out.println("Assessing word block mergeability:");
			for (int b = 0; b < (bibRefs[r].wordBlocks.length-1); b++) {
				if (DEBUG) System.out.println(" - checking '" + bibRefs[r].wordBlocks[b].getValue() + "' and '" + bibRefs[r].wordBlocks[b+1].getValue() + "'");
				for (int t = bibRefs[r].wordBlocks[b].getEndIndex(); t < bibRefs[r].wordBlocks[b+1].getStartIndex(); t++)
					if (bibRefs[r].wordBlockExcluded[t]) {
						canMergeWithSuccessor[b] = false;
						if (DEBUG) System.out.println("   ==> not mergeable due to " + bibRefs[r].structure.details[t] + " '" + bibRefs[r].annotation.valueAt(t) + "'");
						break;
					}
				if (DEBUG && canMergeWithSuccessor[b])
					System.out.println("   ==> mergeable");
			}
			
			//	collect mergeable sequences of word blocks, and score possible splits
			float[] splitAfterWordBlockScores = new float[bibRefs[r].wordBlocks.length];
			Arrays.fill(splitAfterWordBlockScores, 0);
			int wbi = 0;
			if (DEBUG) System.out.println("Assessing word block groupings and splits:");
			while (wbi < bibRefs[r].wordBlocks.length) {
				if (!canMergeWithSuccessor[wbi]) {
					wbi++;
					continue;
				}
				int swbi = wbi;
				while ((wbi < bibRefs[r].wordBlocks.length) && ((wbi == swbi) || canMergeWithSuccessor[wbi-1]))
					wbi++;
				if ((wbi - swbi) >= 3) {
					if (DEBUG) {
						System.out.println(" - investigating group of " + (wbi - swbi) + " word blocks:");
						for (int b = swbi; b < wbi; b++)
							System.out.println("   - " + bibRefs[r].wordBlocks[b].getValue() + " (" + wordBlockScores[b] + ")");
					}
					for (int s = swbi; s < (wbi-1); s++) {
						float sbs = 0;
//						for (int b = swbi; b <= s; b++)
//							sbs += wordBlockScores[b];
//						sbs /= (s-swbi+1);
						for (int b = swbi; b <= s; b++)
							sbs += (wordBlockScores[b] * bibRefs[r].wordBlocks[b].size());
						sbs /= (bibRefs[r].wordBlocks[s].getEndIndex() - bibRefs[r].wordBlocks[swbi].getStartIndex());
						float sas = 0;
//						for (int a = (s+1); a < wbi; a++)
//							sas += wordBlockScores[a];
//						sas /= (wbi-s-1);
						for (int a = (s+1); a < wbi; a++)
							sas += (wordBlockScores[a] * bibRefs[r].wordBlocks[a].size());
						sas /= (bibRefs[r].wordBlocks[wbi-1].getEndIndex() - bibRefs[r].wordBlocks[s+1].getStartIndex());
						
						//	==> product of average quotient and boundary quotient seems to be pretty good indicator
						//		- average quotient = discrimination between blocks of different type
						//		- boundary quotient = entropy of split at specific block boundary
						splitAfterWordBlockScores[s] = (((sbs == 0) ? 1 : (sas/sbs)) * ((wordBlockScores[s] == 0) ? 1 : (wordBlockScores[s+1]/wordBlockScores[s])));
						if (DEBUG) {
							System.out.print(" - split");
							System.out.print(" " + TokenSequenceUtils.concatTokens(bibRefs[r].annotation, bibRefs[r].wordBlocks[swbi].getStartIndex(), (bibRefs[r].wordBlocks[s].getEndIndex() - bibRefs[r].wordBlocks[swbi].getStartIndex())));
							System.out.print("     " + TokenSequenceUtils.concatTokens(bibRefs[r].annotation, bibRefs[r].wordBlocks[s+1].getStartIndex(), (bibRefs[r].wordBlocks[wbi-1].getEndIndex() - bibRefs[r].wordBlocks[s+1].getStartIndex())));
							System.out.println(":");
							System.out.println("   ==> average difference: " + (sas-sbs));
							System.out.println("   ==> average quotient: " + ((sbs == 0) ? 1 : (sas/sbs)));
							System.out.println("   ==> boundary difference: " + (wordBlockScores[s+1]-wordBlockScores[s]));
							System.out.println("   ==> boundary quotient: " + ((wordBlockScores[s] == 0) ? 1 : (wordBlockScores[s+1]/wordBlockScores[s])));
							System.out.println("   ==> score: " + splitAfterWordBlockScores[s]);
						}
					}
				}
				else if (DEBUG) System.out.println(" - skipping group of " + (wbi - swbi) + " word blocks");
			}
			
			//	exclude blocks with two or more digit numbers from journal names (i.e., only if volume designator given)
			if (partDesCount != 0)
				for (int b = 0; b < (bibRefs[r].wordBlocks.length-1); b++) {
					if (bibRefs[r].wordBlocks[b].getEndIndex() >= maxJournalEnd)
						break;
					boolean gotNumber = false;
					for (int t = 0; t < bibRefs[r].wordBlocks[b].size(); t++)
						if ((bibRefs[r].wordBlocks[b].valueAt(t).length() > 1) && Gamta.isNumber(bibRefs[r].wordBlocks[b].valueAt(t))) {
							gotNumber = true;
							break;
						}
					if (gotNumber) {
						minJournalStart = bibRefs[r].wordBlocks[b].getEndIndex();
						if (DEBUG) System.out.println("Word block excluded from journal name: " + bibRefs[r].wordBlocks[b].getValue());
					}
				}
			
			//	prevent lone numbers (word blocks without actual words) from becoming titles by themselves ('1984' is rarely gonna be cited in science)
			for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
				if ((bibRefs[r].bookContentInfos.size() != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxPublisherEnd))
					break;
				if ((partDesCount != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxJournalEnd))
					break;
				boolean gotWord = false;
				for (int t = 0; t < bibRefs[r].wordBlocks[b].size(); t++)
					if ((bibRefs[r].wordBlocks[b].valueAt(t).length() > 1) && Gamta.isWord(bibRefs[r].wordBlocks[b].valueAt(t))) {
						gotWord = true;
						break;
					}
				if (gotWord) {
					minJournalStart = Math.max(minJournalStart, bibRefs[r].wordBlocks[b].getEndIndex());
					minPublisherStart = Math.max(minPublisherStart, bibRefs[r].wordBlocks[b].getEndIndex());
					if (DEBUG) System.out.println("First block containing word included in title: " + bibRefs[r].wordBlocks[b].getValue());
					break;
				}
			}
			
			//	set up classification
			String[] wordBlockMeanings = new String[bibRefs[r].wordBlocks.length];
			Arrays.fill(wordBlockMeanings, null);
			if (DEBUG) System.out.println("Classifying word blocks in " + bibRefs[r].annotation);
			
			//	no volume reference
			if (bibRefs[r].volumeRef == null) {
				if (DEBUG) System.out.println(" - no volume reference given");
				
				//	find last possible start of journal/publisher
				int lJopBlockIndex = 1;
				if (DEBUG) System.out.println(" - got initial JoP start: '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
				
				//	TODO set lJopBlockIndex to start of earliest known JoP
				if (knownJops.length != 0) {
					
					//	rule: no pagination, and known block after proceedings ==> proceedings become title, block afterward becomes publisher (likely reference to proceedings volume)
					
					//	rule: if pagination given, proceedings title and everything after becomes JoP
					
					//	rule: if separator punctutation given and present before proceedings, proceedings title becomes JoP
					
					//	rule: if separator punctutation given and present after proceedings, proceedings title becomes volume title, part afterward become publisher
					
				}
				
				//	TODO restrict to earliest known JoP with separator punctuation before it if latter given
				
				//	rule: if we have a proceedings title, use it and everything after as JoP, but don't expand rightward
				if (proceedingsTitles.length != 0) {
					if (DEBUG) System.out.println(" - got proceedings title: '" + proceedingsTitles[proceedingsTitles.length-1].getValue() + "'");
					for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
						if ((bibRefs[r].bookContentInfos.size() != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxPublisherEnd) && (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
							continue;
						if ((partDesCount != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxJournalEnd) && (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
							continue;
						if (bibRefs[r].wordBlocks[b].getEndIndex() < proceedingsTitles[proceedingsTitles.length-1].getStartIndex())
							wordBlockMeanings[b] = TITLE_ANNOTATION_TYPE;
						else wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
					}
				}
				
				//	no proceedings title or known JoP given, use fuzzy rules
				else {
					
					//	rule: last capitalized block preceding part designator ==> latest possible start for journal/publisher
					if (DEBUG) System.out.println(" - seeking latest possible JoP start");
					for (int b = (bibRefs[r].wordBlocks.length-1); b >= 1; b--) {
						if (bibRefs[r].wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
							if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRefs[r].wordBlocks[b].getValue() + "'");
							break;
						}
						if ((bibRefs[r].bookContentInfos.size() != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxPublisherEnd) && (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
							continue;
						if ((partDesCount != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxJournalEnd) && (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
							continue;
						if (!bibRefs[r].wordBlocks[b].firstValue().matches("[A-Z].*"))
							continue;
						if (this.hasCapWord(bibRefs[r].wordBlocks[b])) {
							lJopBlockIndex = b;
							if (DEBUG) System.out.println(" - latest possible JoP start: '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
							break;
						}
					}
					if (DEBUG) System.out.println(" - got initial JoP start: '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
					
					//	if we have a primary separator, use it
					boolean gotSeparatorStart = false;
					if (tJopSeparatorTokens != null) {
						if (DEBUG) System.out.println(" - seeking backward for JoP with T-JoP separator");
						for (int b = lJopBlockIndex; b >= 1; b--) {
							if ((b != lJopBlockIndex) && !canMergeWithSuccessor[b]) {
								if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRefs[r].wordBlocks[b].getValue() + "'");
								break;
							}
							if (bibRefs[r].wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
								if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRefs[r].wordBlocks[b].getValue() + "'");
								break;
							}
							if (!bibRefs[r].wordBlocks[b].firstValue().matches("[A-Z].*"))
								continue;
							if (TokenSequenceUtils.indexOf(bibRefs[r].annotation, tJopSeparatorTokens, bibRefs[r].wordBlocks[b-1].getEndIndex()) == bibRefs[r].wordBlocks[b-1].getEndIndex()) {
								lJopBlockIndex = b;
								gotSeparatorStart = true;
								if (DEBUG) System.out.println(" - latest possible JoP with T-JoP separator: '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
								break;
							}
						}
					}
					
					//	if we have more occurrences of primary separator further left, use knowledge backed split scoring to extend journal/publisher
					if (DEBUG) System.out.println(" - seeking backward highest scoring split");
					float splitScore = splitAfterWordBlockScores[lJopBlockIndex-1];
					for (int b = (lJopBlockIndex-1); b >= 1; b--) {
						if (!canMergeWithSuccessor[b]) {
							if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRefs[r].wordBlocks[b].getValue() + "'");
							break;
						}
						if (bibRefs[r].wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
							if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRefs[r].wordBlocks[b].getValue() + "'");
							break;
						}
						if (!bibRefs[r].wordBlocks[b].firstValue().matches("[A-Z].*"))
							continue;
						if (!this.hasCapWord(bibRefs[r].wordBlocks[b]))
							continue;
						if (gotSeparatorStart && (tJopSeparatorTokens != null) && TokenSequenceUtils.indexOf(bibRefs[r].annotation, tJopSeparatorTokens, bibRefs[r].wordBlocks[b-1].getEndIndex()) != bibRefs[r].wordBlocks[b-1].getEndIndex())
							continue;
						if (splitScore < splitAfterWordBlockScores[b-1]) {
							lJopBlockIndex = b;
							splitScore = splitAfterWordBlockScores[b-1];
							if (DEBUG) System.out.println("   --> new top scoring JoP start (" + splitAfterWordBlockScores[b-1] + "): '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
						}
					}
					
					//	rule: if journal/publisher can start in second block the earliest, we're done
					//		  + make sure not to span journal/publisher over volume number and pagination
					//		  + if we have no journal/publisher at all (all candidate blocks after stray number mistaken for part designator), use part after
					for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
						if ((bibRefs[r].bookContentInfos.size() != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxPublisherEnd) && (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
							continue;
						if ((partDesCount != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxJournalEnd) && (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
							continue;
						if (b < lJopBlockIndex)
							wordBlockMeanings[b] = TITLE_ANNOTATION_TYPE;
						else wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
					}
				}
			}
			
			//	got volume reference
			else {
				if (DEBUG) System.out.println(" - volume reference given");
				
				//	rule: block before volume ref ==> title
				for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
					if (bibRefs[r].wordBlocks[b].getEndIndex() <= bibRefs[r].volumeRef.annotation.getStartIndex())
						wordBlockMeanings[b] = TITLE_ANNOTATION_TYPE;
					else break;
				}
				
				//	handle word blocks inside volume reference
				ArrayList vrWordBlockList = new ArrayList();
				int firstVrBlockIndex = 0;
				int lastVrBlockIndex = 0;
				for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
					if (bibRefs[r].wordBlocks[b].getEndIndex() <= bibRefs[r].volumeRef.annotation.getStartIndex())
						continue;
					else if (bibRefs[r].wordBlocks[b].getEndIndex() <= bibRefs[r].volumeRef.annotation.getEndIndex()) {
						if (vrWordBlockList.isEmpty())
							firstVrBlockIndex = b;
						lastVrBlockIndex = b;
						vrWordBlockList.add(bibRefs[r].wordBlocks[b]);
					}
					else break;
				}
				
				//	restrict JoP start to end of proceedings titel if latter given, and make everything before volume title
				if (proceedingsTitles.length != 0) {
					minJournalStart = proceedingsTitles[proceedingsTitles.length-1].getEndIndex();
					minPublisherStart = proceedingsTitles[proceedingsTitles.length-1].getEndIndex();
				}
				
				//	restrict to earliest known JoP with separator punctuation before it if latter given
				else if ((knownJops.length != 0) && (tJopSeparatorTokens != null)) {
					for (int j = 0; j < knownJops.length; j++) {
						if (knownJops[j].getStartIndex() < tJopSeparatorTokens.size())
							continue;
						if (!AnnotationUtils.liesIn(knownJops[j], bibRefs[r].volumeReference))
							continue;
						if (TokenSequenceUtils.indexOf(bibRefs[r].annotation, tJopSeparatorTokens, (knownJops[j].getStartIndex() - tJopSeparatorTokens.size())) == (knownJops[j].getStartIndex() - tJopSeparatorTokens.size())) {
							minJournalStart = knownJops[j].getStartIndex();
							minPublisherStart = knownJops[j].getStartIndex();
							break;
						}
					}
				}
				
				//	rule: first block in volume ref ==> volume title
				wordBlockMeanings[firstVrBlockIndex] = VOLUME_TITLE_ANNOTATION_TYPE;
				
				//	find last possible start of journal/publisher
				int lJopBlockIndex = firstVrBlockIndex+1;
				if (DEBUG && (lJopBlockIndex < bibRefs[r].wordBlocks.length))
					System.out.println(" - got initial JoP start: '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
				
				//	rule: last capitalized block preceding part designator ==> latest start for journal/publisher
				if (DEBUG) System.out.println(" - seeking latest possible JoP start");
				for (int b = lastVrBlockIndex; b >= (firstVrBlockIndex+1); b--) {
					if (bibRefs[r].wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
						if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRefs[r].wordBlocks[b].getValue() + "'");
						break;
					}
					if ((bibRefs[r].bookContentInfos.size() != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxPublisherEnd) &&  (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxPublisherEnd))
						continue;
					if ((partDesCount != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxJournalEnd) && (bibRefs[r].wordBlocks[lJopBlockIndex].getStartIndex() < maxJournalEnd))
						continue;
					if (!bibRefs[r].wordBlocks[b].firstValue().matches("[A-Z].*"))
						continue;
					if (this.hasCapWord(bibRefs[r].wordBlocks[b])) {
						lJopBlockIndex = b;
						if (DEBUG) System.out.println(" - latest possible JoP start: '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
						break;
					}
				}
				
				//	if we have a primary separator, use it
				boolean gotSeparatorStart = false;
				if (tJopSeparatorTokens != null) {
					if (DEBUG) System.out.println(" - seeking backward for JoP with T-JoP separator '" + tJopSeparator + "'");
					for (int b = lJopBlockIndex; b >= (firstVrBlockIndex+1); b--) {
						if (b >= bibRefs[r].wordBlocks.length)
							continue; // we need this catch here in case separator doesn't occur at all and bounds reach beyond array size
						if ((b != lJopBlockIndex) && !canMergeWithSuccessor[b]) {
							if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRefs[r].wordBlocks[b].getValue() + "'");
							break;
						}
						if (bibRefs[r].wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
							if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRefs[r].wordBlocks[b].getValue() + "'");
							break;
						}
						if (!bibRefs[r].wordBlocks[b].firstValue().matches("[A-Z].*"))
							continue;
						if (TokenSequenceUtils.indexOf(bibRefs[r].annotation, tJopSeparatorTokens, bibRefs[r].wordBlocks[b-1].getEndIndex()) == bibRefs[r].wordBlocks[b-1].getEndIndex()) {
							lJopBlockIndex = b;
							gotSeparatorStart = true;
							if (DEBUG) System.out.println(" - latest possible JoP with T-JoP separator: '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
							break;
						}
					}
				}
				
				//	if we have more occurrences of primary separator further left, use knowledge backed split scoring to extend journal/publisher
				if (DEBUG) System.out.println(" - seeking backward highest scoring split");
				float splitScore = splitAfterWordBlockScores[lJopBlockIndex-1];
				for (int b = (lJopBlockIndex-1); b >= (firstVrBlockIndex+1); b--) {
					if (!canMergeWithSuccessor[b]) {
						if (DEBUG) System.out.println(" - giving up at unattachable block: '" + bibRefs[r].wordBlocks[b].getValue() + "'");
						break;
					}
					if (bibRefs[r].wordBlocks[b].getStartIndex() < Math.max(minJournalStart, minPublisherStart)) {
						if (DEBUG) System.out.println(" - giving up at block starting before " + Math.max(minJournalStart, minPublisherStart) + ": '" + bibRefs[r].wordBlocks[b].getValue() + "'");
						break;
					}
					if (!bibRefs[r].wordBlocks[b].firstValue().matches("[A-Z].*"))
						continue;
					if (gotSeparatorStart && (tJopSeparatorTokens != null) && TokenSequenceUtils.indexOf(bibRefs[r].annotation, tJopSeparatorTokens, bibRefs[r].wordBlocks[b-1].getEndIndex()) != bibRefs[r].wordBlocks[b-1].getEndIndex())
						continue;
					if (splitScore < splitAfterWordBlockScores[b-1]) {
						lJopBlockIndex = b;
						splitScore = splitAfterWordBlockScores[b-1];
						if (DEBUG) System.out.println(" - new top scoring JoP start (" + splitAfterWordBlockScores[b-1] + "): '" + bibRefs[r].wordBlocks[lJopBlockIndex].getValue() + "'");
					}
				}
				
				//	rule: if journal/publisher can start in second block the earlies, we're done
				//		  + make sure not to span journal/publisher over volume number and pagination
				for (int b = firstVrBlockIndex; b <= lastVrBlockIndex; b++) {
					if ((bibRefs[r].bookContentInfos.size() != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxPublisherEnd))
						continue;
					if ((partDesCount != 0) && (bibRefs[r].wordBlocks[b].getEndIndex() > maxJournalEnd))
						continue;
					if (b < lJopBlockIndex)
						wordBlockMeanings[b] = VOLUME_TITLE_ANNOTATION_TYPE;
					else wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
				}
				
				//	go looking for possible publishers after pagination
				for (int b = (lastVrBlockIndex+1); b < bibRefs[r].wordBlocks.length; b++)
					wordBlockMeanings[b] = JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE;
				
				//	TODO if known JoP found after pagination, use it, and include all word blocks inside volume reference in volume title
			}
			
			if (DEBUG) {
				System.out.println("Word blocks classified:");
				for (int b = 0; b < bibRefs[r].wordBlocks.length; b++)
					System.out.println(" - " + wordBlockMeanings[b] + ": " + bibRefs[r].wordBlocks[b].getValue());
			}
			
			//	annotate what we have, and deal with multiple titles and journals/publishers
			int start = -1;
			float jopScoreSum = 0;
			ArrayList titles = new ArrayList(2);
			ArrayList volumeTitles = new ArrayList(2);
			ArrayList jops = new ArrayList(2);
			for (int b = 0; b < bibRefs[r].wordBlocks.length; b++) {
				if (wordBlockMeanings[b] == null)
					continue;
				if (start == -1)
					start = bibRefs[r].wordBlocks[b].getStartIndex();
				jopScoreSum += wordBlockScores[b];
				if (canMergeWithSuccessor[b] && ((b+1) < bibRefs[r].wordBlocks.length) && wordBlockMeanings[b].equals(wordBlockMeanings[b+1]))
					continue;
				Annotation typeAnnot = Gamta.newAnnotation(bibRefs[r].annotation, wordBlockMeanings[b], start, (bibRefs[r].wordBlocks[b].getEndIndex() - start));
//				if (TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRefs[r].title == null))
//					bibRefs[r].title = typeAnnot;
				if (TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRefs[r].title == null))
					titles.add(typeAnnot);
//				else if (VOLUME_TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRefs[r].volumeTitle == null))
//					bibRefs[r].volumeTitle = typeAnnot;
				else if (VOLUME_TITLE_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRefs[r].volumeTitle == null))
					volumeTitles.add(typeAnnot);
//				else if (JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRefs[r].journalOrPublisher == null))
//					bibRefs[r].journalOrPublisher = typeAnnot;
				else if (JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE.equals(wordBlockMeanings[b]) && (bibRefs[r].journalOrPublisher == null))
					jops.add(typeAnnot);
				typeAnnot.setAttribute("jopScore", ("" + jopScoreSum));
				if (DEBUG) System.out.println(" - " + typeAnnot.toXML());
				start = -1;
			}
			
			//	handle multiple titles if given
			if (titles.size() == 1)
				bibRefs[r].title = ((Annotation) titles.remove(0));
			else if (titles.size() != 0) {
				if (DEBUG) System.out.println("Picking title from " + titles.size() + " candidates:");
//				String[] inferredTypes = new String[titles.size()];
//				int[] inferredTypeScores = new int[titles.size()];
				for (int t = 0; t < titles.size(); t++) {
					Annotation title = ((Annotation) titles.get(t));
					String beforeType = "|";
					String afterType = "|";
					StringVector types = new StringVector();
					StringIndex typeCounts = new StringIndex();
					if (DEBUG) System.out.println(" - investigating '" + title.getValue() + "'");
					for (int b = (title.getStartIndex()-1); b >= 0; b--)
						if (!"_".equals(bibRefs[r].structure.details[b])) {
							beforeType = bibRefs[r].structure.details[b];
							if (DEBUG) System.out.println("   - before type is " + beforeType);
							break;
						}
					for (int a = title.getEndIndex(); a < bibRefs[r].annotation.size(); a++)
						if (!"_".equals(bibRefs[r].structure.details[a])) {
							afterType = bibRefs[r].structure.details[a];
							if (DEBUG) System.out.println("   - after type is " + afterType);
							break;
						}
					for (int s = 0; s < bibRefs.length; s++) {
						if (s == r)
							continue;
						for (int i = 0; i < bibRefs[s].structure.punctSummary.length; i++) {
							if (beforeType.equals(bibRefs[s].structure.punctSummary[i])) {
								for (int a = (i+1); a < bibRefs[s].structure.punctSummary.length; a++)
									if ("_".equals(bibRefs[s].structure.punctSummary[a]) || !Gamta.isPunctuation(bibRefs[s].structure.punctSummary[a])) {
										types.addElementIgnoreDuplicates(bibRefs[s].structure.punctSummary[a]);
										typeCounts.add(bibRefs[s].structure.punctSummary[a]);
										break;
									}
							}
							if (afterType.equals(bibRefs[s].structure.punctSummary[i])) {
								for (int b = (i-1); b >= 0; b--)
									if ("_".equals(bibRefs[s].structure.punctSummary[b]) || !Gamta.isPunctuation(bibRefs[s].structure.punctSummary[b])) {
										types.addElementIgnoreDuplicates(bibRefs[s].structure.punctSummary[b]);
										typeCounts.add(bibRefs[s].structure.punctSummary[b]);
										break;
									}
							}
						}
					}
					if (DEBUG) System.out.println(" - types after " + beforeType + " / before " + afterType + ":");
					int inferredTypeScore = 0;
					for (int y = 0; y < types.size(); y++) {
						String type = types.get(y);
						int typeScore = typeCounts.getCount(type);
						if (DEBUG) System.out.println("   - " + type + " " + typeScore);
						if (typeScore > inferredTypeScore) {
							title.setAttribute(TYPE_ATTRIBUTE, type);
							title.setAttribute((TYPE_ATTRIBUTE + "Score"), ("" + typeScore));
							inferredTypeScore = typeScore;
							if (DEBUG) System.out.println("     ==> new top type");
						}
					}
				}
				
				int maxTitleScore = -1;
				for (int t = 0; t < titles.size(); t++) {
					Annotation title = ((Annotation) titles.get(t));
					if ("_".equals(title.getAttribute(TYPE_ATTRIBUTE))) {
						int titleScore = Integer.parseInt((String) title.getAttribute((TYPE_ATTRIBUTE + "Score"), "0"));
						if (maxTitleScore < titleScore) {
							bibRefs[r].title = title;
							maxTitleScore = titleScore;
						}
					}
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(title.getAttribute(TYPE_ATTRIBUTE)) && (bibRefs[r].authorList == null)) {
						bibRefs[r].authors = new Annotation[1];
						bibRefs[r].authors[0] = Gamta.newAnnotation(bibRefs[r].annotation, AUTHOR_ANNOTATION_TYPE, title.getStartIndex(), title.size());
						titles.remove(t--);
					}
					else if (EDITOR_LIST_ANNOTATION_TYPE.equals(title.getAttribute(TYPE_ATTRIBUTE))) {
						bibRefs[r].editors = new Annotation[1];
						bibRefs[r].editors[0] = Gamta.newAnnotation(bibRefs[r].annotation, EDITOR_ANNOTATION_TYPE, title.getStartIndex(), title.size());
						titles.remove(t--);
					}
				}
				
				for (int t = 0; t < titles.size(); t++) {
					if (titles.get(t) == bibRefs[r].title)
						titles.remove(t--);
				}
			}
			
			//	handle multiple volume titles if given
			if (volumeTitles.size() != 0)
				bibRefs[r].volumeTitle = ((Annotation) volumeTitles.remove(0));
			
			//	two candidate volume titles, but no journal/publisher, recycle remaining volume title
			if ((jops.size() == 0) && (volumeTitles.size() != 0)) {
				jops.addAll(volumeTitles);
				volumeTitles.clear();
				if (DEBUG) System.out.println("Re-purposed remaining volume titles as journal/publisher candidates for lack of alternatives");
			}
			
			//	two candidate titles, but no journal/publisher, recycle remaining title
			if ((jops.size() == 0) && (titles.size() != 0)) {
				jops.addAll(titles);
				titles.clear();
				if (DEBUG) System.out.println("Re-purposed remaining titles as journal/publisher candidates for lack of alternatives");
			}
			
			//	handle multiple journals/publishers if given
			if (jops.size() == 1)
				bibRefs[r].journalOrPublisher = ((Annotation) jops.remove(0));
			else if (jops.size() != 0) {
				if (DEBUG) System.out.println("Picking journal/publisher from " + jops.size() + " candidates:");
//				String[] inferredTypes = new String[jops.size()];
//				int[] inferredTypeScores = new int[jops.size()];
				for (int j = 0; j < jops.size(); j++) {
					
					//	TODO also consider word block score
					
					//	TODO also use 'knownJoP' markers
					
					Annotation jop = ((Annotation) jops.get(j));
					String beforeType = "|";
					String afterType = "|";
					StringVector types = new StringVector();
					StringIndex typeCounts = new StringIndex();
					if (DEBUG) System.out.println(" - investigating '" + jop.getValue() + "'");
					for (int b = (jop.getStartIndex()-1); b >= 0; b--)
						if (!"_".equals(bibRefs[r].structure.details[b])) {
							beforeType = bibRefs[r].structure.details[b];
							if (DEBUG) System.out.println("   - before type is " + beforeType);
							break;
						}
					for (int a = jop.getEndIndex(); a < bibRefs[r].annotation.size(); a++)
						if (!"_".equals(bibRefs[r].structure.details[a])) {
							afterType = bibRefs[r].structure.details[a];
							if (DEBUG) System.out.println("   - after type is " + afterType);
							break;
						}
					for (int s = 0; s < bibRefs.length; s++) {
						if (s == r)
							continue;
						for (int i = 0; i < bibRefs[s].structure.punctSummary.length; i++) {
							if (beforeType.equals(bibRefs[s].structure.punctSummary[i])) {
								for (int a = (i+1); a < bibRefs[s].structure.punctSummary.length; a++)
									if ("_".equals(bibRefs[s].structure.punctSummary[a]) || !Gamta.isPunctuation(bibRefs[s].structure.punctSummary[a])) {
										types.addElementIgnoreDuplicates(bibRefs[s].structure.punctSummary[a]);
										typeCounts.add(bibRefs[s].structure.punctSummary[a]);
										break;
									}
							}
							if (afterType.equals(bibRefs[s].structure.punctSummary[i])) {
								for (int b = (i-1); b >= 0; b--)
									if ("_".equals(bibRefs[s].structure.punctSummary[b]) || !Gamta.isPunctuation(bibRefs[s].structure.punctSummary[b])) {
										types.addElementIgnoreDuplicates(bibRefs[s].structure.punctSummary[b]);
										typeCounts.add(bibRefs[s].structure.punctSummary[b]);
										break;
									}
							}
						}
					}
					if (DEBUG) System.out.println(" - types after " + beforeType + " / before " + afterType + ":");
					int inferredTypeScore = 0;
					for (int y = 0; y < types.size(); y++) {
						String type = types.get(y);
						int typeScore = typeCounts.getCount(type);
						if (DEBUG) System.out.println("   - " + type + " " + typeScore);
						if (typeScore > inferredTypeScore) {
							jop.setAttribute(TYPE_ATTRIBUTE, type);
							jop.setAttribute((TYPE_ATTRIBUTE + "Score"), ("" + typeScore));
							inferredTypeScore = typeScore;
							if (DEBUG) System.out.println("     ==> new top type");
						}
					}
				}
				
				int maxJopScore = -1;
				for (int j = 0; j < jops.size(); j++) {
					Annotation jop = ((Annotation) jops.get(j));
					if ("_".equals(jop.getAttribute(TYPE_ATTRIBUTE))) {
						int jopScore = Integer.parseInt((String) jop.getAttribute((TYPE_ATTRIBUTE + "Score"), "0"));
						if (maxJopScore < jopScore) {
							bibRefs[r].journalOrPublisher = jop;
							maxJopScore = jopScore;
						}
					}
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(jop.getAttribute(TYPE_ATTRIBUTE)) && (bibRefs[r].authorList == null)) {
						bibRefs[r].authors = new Annotation[1];
						bibRefs[r].authors[0] = Gamta.newAnnotation(bibRefs[r].annotation, AUTHOR_ANNOTATION_TYPE, jop.getStartIndex(), jop.size());
						jops.remove(j--);
					}
					else if (EDITOR_LIST_ANNOTATION_TYPE.equals(jop.getAttribute(TYPE_ATTRIBUTE))) {
						bibRefs[r].editors = new Annotation[1];
						bibRefs[r].editors[0] = Gamta.newAnnotation(bibRefs[r].annotation, EDITOR_ANNOTATION_TYPE, jop.getStartIndex(), jop.size());
						jops.remove(j--);
					}
				}
				
				for (int j = 0; j < jops.size(); j++) {
					if (jops.get(j) == bibRefs[r].journalOrPublisher)
						jops.remove(j--);
				}
			}
			
			//	if non-selected title adjacent to JoP, merge the two
			if (titles.size() != 0) {
				if (DEBUG) System.out.println("Handling remaining candidate titles:");
				if (bibRefs[r].journalOrPublisher == null) {
					bibRefs[r].journalOrPublisher = ((Annotation) titles.remove(0));
					if (DEBUG) System.out.println(" - " + bibRefs[r].journalOrPublisher.toXML());
					if (DEBUG) System.out.println(" ==> filled in for lacking journal/publisher: " + bibRefs[r].journalOrPublisher.toXML());
				}
				for (int t = (titles.size() - 1); t >= 0; t--) {
					Annotation title = ((Annotation) titles.get(t));
					if (DEBUG) System.out.println(" - " + title.toXML());
					if (bibRefs[r].journalOrPublisher.getStartIndex() < title.getEndIndex()) {
						if (DEBUG) System.out.println(" --> cannot attach, too late in reference");
						continue;
					}
					if (!title.firstValue().matches("[A-Z].*")) {
						if (DEBUG) System.out.println(" --> cannot attach, lower case start");
						continue;
					}
					boolean canMerge = true;
					for (int b = title.getEndIndex(); b < bibRefs[r].journalOrPublisher.getStartIndex(); b++)
						if (!"_".equals(bibRefs[r].structure.details[b]) && !Gamta.isPunctuation(bibRefs[r].annotation.valueAt(b))) {
							canMerge = false;
							if (DEBUG) System.out.println(" --> cannot attach due to intermediate " + bibRefs[r].structure.details[b] + ": " + bibRefs[r].annotation.valueAt(b));
							break;
						}
					if (canMerge) {
						Annotation jop = Gamta.newAnnotation(bibRefs[r].annotation, JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE, title.getStartIndex(), (bibRefs[r].journalOrPublisher.getEndIndex() - title.getStartIndex()));
						jop.copyAttributes(bibRefs[r].journalOrPublisher);
						bibRefs[r].journalOrPublisher = jop;
						if (DEBUG) System.out.println(" ==> attached to journal/publisher: " + bibRefs[r].journalOrPublisher.toXML());
					}
				}
			}
			
			//	if non-selected volume title adjacent to JoP, merge the two
			if (volumeTitles.size() != 0) {
				if (DEBUG) System.out.println("Handling remaining candidate volume titles:");
				if (bibRefs[r].journalOrPublisher == null) {
					bibRefs[r].journalOrPublisher = ((Annotation) volumeTitles.remove(0));
					if (DEBUG) System.out.println(" - " + bibRefs[r].journalOrPublisher.toXML());
					if (DEBUG) System.out.println(" ==> filled in for lacking journal/publisher: " + bibRefs[r].journalOrPublisher.toXML());
				}
				for (int t = (volumeTitles.size() - 1); t >= 0; t--) {
					Annotation volumeTitle = ((Annotation) volumeTitles.get(t));
					if (DEBUG) System.out.println(" - " + volumeTitle.toXML());
					if (bibRefs[r].journalOrPublisher.getStartIndex() < volumeTitle.getEndIndex()) {
						if (DEBUG) System.out.println(" --> cannot attach, too late in reference");
						continue;
					}
					if (!volumeTitle.firstValue().matches("[A-Z].*")) {
						if (DEBUG) System.out.println(" --> cannot attach, lower case start");
						continue;
					}
					boolean canMerge = true;
					for (int b = volumeTitle.getEndIndex(); b < bibRefs[r].journalOrPublisher.getStartIndex(); b++)
						if (!"_".equals(bibRefs[r].structure.details[b]) && !Gamta.isPunctuation(bibRefs[r].annotation.valueAt(b))) {
							canMerge = false;
							if (DEBUG) System.out.println(" --> cannot attach due to intermediate " + bibRefs[r].structure.details[b] + ": " + bibRefs[r].annotation.valueAt(b));
							break;
						}
					if (canMerge) {
						Annotation jop = Gamta.newAnnotation(bibRefs[r].annotation, JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE, volumeTitle.getStartIndex(), (bibRefs[r].journalOrPublisher.getEndIndex() - volumeTitle.getStartIndex()));
						jop.copyAttributes(bibRefs[r].journalOrPublisher);
						bibRefs[r].journalOrPublisher = jop;
						if (DEBUG) System.out.println(" ==> attached to journal/publisher: " + bibRefs[r].journalOrPublisher.toXML());
					}
				}
			}
			
			//	get rid of volume reference
			AnnotationFilter.removeAnnotations(bibRefs[r].annotation, VOLUME_REFERENCE_ANNOTATION_TYPE);
		}
//		
//		
//		//	split remainder of references (parts not assigned by structures) into titles for paper and journal, or book title and publisher name, respectively
//		for (int r = 0; r < bibRefs.length; r++) {
//			if (bibRefs[r].preExistingStructure)
//				continue;
//			this.getTitleAndOrigin(bibRefs[r], primarySeparator);
//		}
		
		//	guess type and set respective annotation attribute
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].type != null)
				continue;
			this.classify(bibRefs[r]);
		}
		
		//	further split or classify origin (not in volume references, as main call gets here after returning from integrated recursion, and generic origin passes on more easily)
		if (detailOrigin) {
			for (int r = 0; r < bibRefs.length; r++)
				this.parseOrigin(bibRefs[r], primarySeparator);
		}
		
		//	transfer annotations to references
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].preExistingStructure)
				continue;
			this.annotateDetails(bibRefs[r]);
		}
		
		return authorListStyle;
	}
	
	private boolean hasCapWord(Annotation wordBlock) {
		String bracket = null;
		for (int t = 0; t < wordBlock.size(); t++) {
			String v = wordBlock.valueAt(t);
			if (bracket != null) {
				if (Gamta.closes(v, bracket))
					bracket = null;
				continue;
			}
			if (this.journalPublisherStopWords.containsIgnoreCase(v))
				continue;
			if (Gamta.isRomanNumber(v))
				continue;
			if (Gamta.isOpeningBracket(v)) {
				bracket = v;
				continue;
			}
			if (v.length() < 2)
				continue;
			if (Character.toLowerCase(v.charAt(0)) == v.charAt(0))
				continue;
			for (int c = 0; c < v.length(); c++) {
				if ("AEIOUYaeiouy".indexOf(v.charAt(c)) != -1)
					return true;
			}
		}
		return false;
	}
	
	private boolean hasVowel(Annotation annot) {
		for (int t = 0; t < annot.size(); t++) {
			String v = annot.valueAt(t);
			for (int c = 0; c < v.length(); c++) {
				if ("AEIOUYaeiouy".indexOf(v.charAt(c)) != -1)
					return true;
			}
		}
		return false;
	}
	
	private Annotation[] getKnownJops(BibRef bibRef) {
		ArrayList knownJopList = new ArrayList();
		if (DEBUG) System.out.println("Getting known journals/publishers from " + bibRef.annotation.toXML());
		
		//	do lexicon lookups (not first block, that one's definitely part of the title)
		if (DEBUG) System.out.println("  - journal/publisher names from dictionary:");
		for (int b = 1; b < bibRef.wordBlocks.length; b++) {
			if (!this.hasCapWord(bibRef.wordBlocks[b]))
				continue;
			if (this.knownJournalsAndPublishers.lookup(TokenSequenceUtils.concatTokens(bibRef.wordBlocks[b], true, true))) {
				if (DEBUG) System.out.println("    - " + bibRef.wordBlocks[b]);
				bibRef.wordBlocks[b].setAttribute("isKnown", "true");
				knownJopList.add(bibRef.wordBlocks[b]);
			}
			for (int l = (b+1); l < bibRef.wordBlocks.length; l++) {
				if ((bibRef.wordBlocks[l].getStartIndex() - bibRef.wordBlocks[l-1].getEndIndex()) > 1)
					break;
				if (this.knownJournalsAndPublishers.lookup(TokenSequenceUtils.concatTokens(bibRef.annotation, bibRef.wordBlocks[b].getStartIndex(), (bibRef.wordBlocks[l].getEndIndex() - bibRef.wordBlocks[b].getStartIndex()), true, true))) {
					Annotation knownJop = Gamta.newAnnotation(bibRef.annotation, null, bibRef.wordBlocks[b].getStartIndex(), (bibRef.wordBlocks[l].getEndIndex() - bibRef.wordBlocks[b].getStartIndex()));
					if (DEBUG) System.out.println("    - " + knownJop);
					knownJop.setAttribute("isKnown", "true");
					knownJopList.add(knownJop);
				}
			}
		}
		
		Collections.sort(knownJopList);
		return ((Annotation[]) knownJopList.toArray(new Annotation[knownJopList.size()]));
	}
	
	private Annotation[] getProceedingsTitles(BibRef bibRef) {
		ArrayList knownJopList = new ArrayList();
		
		//	get years (might come from parent reference)
		Annotation[] yearAnnots = ((bibRef.parentRef == null) ? bibRef.years : bibRef.parentRef.years);
		Annotation yearAnnot = ((bibRef.parentRef == null) ? bibRef.year : bibRef.parentRef.year);
		
		//	use pattern to find proceedings title from correct year
		if ((yearAnnots != null) && (yearAnnot != null) && (yearAnnot.length() == 4)) {
			String year = yearAnnot.getValue();
			String yearRegEx;
			if (yearAnnots.length > 1)
				yearRegEx = (year + "|\\'?" + year.substring(2));
			else yearRegEx = ("\\'?" + year.substring(2));
			Annotation[] proceedingsTitles = Gamta.extractAllMatches(bibRef.annotation, ("(Proc(\\.|eedings))[^0-9]+(" + yearRegEx + ")"), true);
			if (DEBUG) {
				System.out.println("  - proceedings titles for year " + year + ":");
				for (int p = 0; p < proceedingsTitles.length; p++)
					System.out.println("    - " + proceedingsTitles[p]);
			}
			if (proceedingsTitles.length == 0) try {
				year = ("" + (Integer.parseInt(yearAnnot.getValue()) - 1));
				if (yearAnnots.length > 1)
					yearRegEx = (year + "|\\'?" + year.substring(2));
				else yearRegEx = ("\\'?" + year.substring(2));
				proceedingsTitles = Gamta.extractAllMatches(bibRef.annotation, ("(Proc(\\.|eedings))[^0-9]+(" + yearRegEx + ")"), true);
				if (DEBUG) {
					System.out.println("  - proceedings titles for year " + year + ":");
					for (int p = 0; p < proceedingsTitles.length; p++)
						System.out.println("    - " + proceedingsTitles[p]);
				}
			} catch (NumberFormatException nfe) {}
			for (int p = 0; p < proceedingsTitles.length; p++) {
				proceedingsTitles[p].setAttribute("isProceedings", "true");
				knownJopList.add(proceedingsTitles[p]);
			}
		}
		
		Collections.sort(knownJopList);
		return ((Annotation[]) knownJopList.toArray(new Annotation[knownJopList.size()]));
	}
	
	private float getJopScore(Annotation wordBlock) {
		float js = 0;
		int jwc = 0;
		for (int t = 0; t < wordBlock.size(); t++) {
			String v = wordBlock.valueAt(t);
			if (Gamta.isWord(v)) {
				js += this.jopWordStat.getScore(v, (t == 0), ((t+1) == wordBlock.size()));
				jwc++;
			}
		}
		return ((jwc == 0) ? 0 : (js / jwc));
	}
	
	private static class WordUseData {
		String word;
		int count = 0;
		int jopCount = 0;
		int jopStartCount = 0;
		int jopEndCount = 0;
		WordUseData(String word) {
			this.word = word;
		}
		WordUseData(String word, int count, int jopCount, int jopStartCount, int jopEndCount) {
			this.word = word;
			this.count = count;
			this.jopCount = jopCount;
			this.jopStartCount = jopStartCount;
			this.jopEndCount = jopEndCount;
		}
		void count(boolean inJop, boolean jopStart, boolean jopEnd) {
			this.count++;
			if (inJop) {
				this.jopCount++;
				if (jopStart)
					this.jopStartCount++;
				if (jopEnd)
					this.jopEndCount++;
			}
		}
		float getScore(boolean jopStart, boolean jopEnd) {
			if ((this.count == 0) || (this.jopCount == 0))
				return 0;
			return (((float) (this.jopCount + (jopStart ? this.jopStartCount : 0) + (jopEnd ? this.jopEndCount : 0))) / this.count);
		}
		String toDataString() {
			return (this.word + "|" + this.count + "|" + this.jopCount + "|" + this.jopStartCount + "|" + this.jopEndCount);
		}
	}
	private static class WordUseStat {
		TreeMap wordStats = new TreeMap(String.CASE_INSENSITIVE_ORDER);
		boolean dirty = false;
		void count(String word, boolean inJop, boolean jopStart, boolean jopEnd) {
			WordUseData wud = ((WordUseData) this.wordStats.get(word));
			if (wud == null) {
				wud = new WordUseData(word);
				this.wordStats.put(word, wud);
			}
			wud.count(inJop, jopStart, jopEnd);
			this.dirty = true;
		}
		float getScore(String word, boolean jopStart, boolean jopEnd) {
			WordUseData wud = ((WordUseData) this.wordStats.get(word));
			if (wud == null)
				return 0;
			return wud.getScore(jopStart, jopEnd);
		}
		boolean isDirty() {
			return this.dirty;
		}
		void writeData(BufferedWriter bw) throws IOException {
			for (Iterator wit = this.wordStats.keySet().iterator(); wit.hasNext();) {
				WordUseData wud = ((WordUseData) this.wordStats.get(wit.next()));
				bw.write(wud.toDataString());
				bw.newLine();
			}
			bw.flush();
			this.dirty = false;
		}
		void readData(BufferedReader br) throws IOException {
			String dl;
			while ((dl = br.readLine()) != null) {
				String[] d = dl.split("\\|");
				if (d.length == 5)
					this.wordStats.put(d[0], new WordUseData(d[0], Integer.parseInt(d[1]), Integer.parseInt(d[2]), Integer.parseInt(d[3]), Integer.parseInt(d[4])));
			}
		}
	}
	
	private void getWordBlocks(BibRef bibRef) {
		if (DEBUG) System.out.println("Getting word blocks from " + bibRef.annotation.toXML());
		
		//	summarize existing structure for filtering
		bibRef.wordBlockExcluded = new boolean[bibRef.annotation.size()];
		Arrays.fill(bibRef.wordBlockExcluded, false);
		for (int u = 0; u < bibRef.urls.length; u++) {
			for (int t = bibRef.urls[u].getStartIndex(); t < bibRef.urls[u].getEndIndex(); t++)
				bibRef.wordBlockExcluded[t] = true;
			if (DEBUG) System.out.println(" - excluding URL '" + bibRef.urls[u].getValue() + "'");
		}
		for (int d = 0; d < bibRef.dois.length; d++) {
			for (int t = bibRef.dois[d].getStartIndex(); t < bibRef.dois[d].getEndIndex(); t++)
				bibRef.wordBlockExcluded[t] = true;
			if (DEBUG) System.out.println(" - excluding DOI '" + bibRef.dois[d].getValue() + "'");
		}
		for (int t = 0; t < bibRef.structure.details.length; t++)
			if (!"_".equals(bibRef.structure.details[t])) {
				if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(bibRef.structure.details[t]) && bibRef.annotation.valueAt(t).matches("[A-Zz-z]")) {
					if (DEBUG) System.out.println(" - ignoring part designator letter '" + bibRef.annotation.valueAt(t) + "'");
					continue;
				}
				bibRef.wordBlockExcluded[t] = true;
				if (DEBUG) System.out.println(" - excluding token assigned as " + bibRef.structure.details[t] + " '" + bibRef.annotation.valueAt(t) + "'");
			}
		for (int i = 0; i < bibRef.bookContentInfos.size(); i++) {
			Annotation bci = ((Annotation) bibRef.bookContentInfos.get(i));
			for (int t = bci.getStartIndex(); t < bci.getEndIndex(); t++)
				bibRef.wordBlockExcluded[t] = true;
			if (DEBUG) System.out.println(" - excluding book content info '" + bci.getValue() + "'");
		}
		
		//	get word blocks
		ArrayList wordBlocks = new ArrayList();
		
		//	we've seen this one before, use what's there
		if (bibRef.preExistingStructure) {
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(TITLE_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(VOLUME_TITLE_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(JOURNAL_NAME_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(PUBLISHER_ANNOTATION_TYPE)));
			wordBlocks.addAll(Arrays.asList(bibRef.annotation.getAnnotations(LOCATION_ANNOTATION_TYPE)));
		}
		
		//	this one's new
		else {
			
			//	get abbreviation blocks as a whole
			wordBlocks.addAll(Arrays.asList(this.getTitleCaseAbbreviationBlocks(bibRef.annotation, bibRef.wordBlockExcluded)));
			
			//	get word blocks delimited by punctuation
			int wordBlockStart = -1;
			for (int t = 0; t < bibRef.annotation.size(); t++) {
				if (DEBUG && bibRef.wordBlockExcluded[t])
					System.out.println(" - skipping over non-title token '" + bibRef.annotation.valueAt(t) + "'");
				if (Gamta.isPunctuation(bibRef.annotation.valueAt(t)) || bibRef.wordBlockExcluded[t]) {
					if (wordBlockStart != -1)
						wordBlocks.add(Gamta.newAnnotation(bibRef.annotation, null, wordBlockStart, (t-wordBlockStart)));
					wordBlockStart = -1;
				}
				else if (wordBlockStart == -1)
					wordBlockStart = t;
			}
			if (wordBlockStart != -1)
				wordBlocks.add(Gamta.newAnnotation(bibRef.annotation, null, wordBlockStart, (bibRef.annotation.size()-wordBlockStart)));
			
			//	sort out blocks consisting of punctuation marks only, and individual lower case letters
			for (int w = 0; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w));
				boolean punctuationOnly = true;
				for (int t = wb.getStartIndex(); t < wb.getEndIndex(); t++) {
					String v = bibRef.annotation.valueAt(t);
					if ((Gamta.isWord(v) && !v.matches("[a-z]")) || Gamta.isNumber(v)) {
						punctuationOnly = false;
						break;
					}
				}
				if (punctuationOnly) {
					if (DEBUG)
						System.out.println(" - removing punctuation-only word block '" + wb.getValue() + "'");
					wordBlocks.remove(w--);
				}
			}
			
			//	truncate leading single Latin lower case letter if preceded by year and followed by capitalized word
			for (int w = 0; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w));
				if (wb.size() < 2)
					continue;
				if (wb.getStartIndex() < 1)
					continue;
				if (!wb.firstValue().matches("[a-z]"))
					continue;
				if (!wb.valueAt(1).matches("[A-Z].*"))
					continue;
				if (!bibRef.annotation.valueAt(wb.getStartIndex()-1).matches("[12][0-9]{3}"))
					continue;
				if (DEBUG)
					System.out.println(" - truncating index letter off word block '" + wb.getValue() + "'");
				wb = Gamta.newAnnotation(bibRef.annotation, null, (wb.getStartIndex() + 1), (wb.size() - 1));
				wordBlocks.set(w, wb);
				if (DEBUG)
					System.out.println("   --> '" + wb.getValue() + "'");
			}
			
			//	sort out blocks covered by others
			Collections.sort(wordBlocks);
			for (int w = 1; w < wordBlocks.size(); w++) {
				Annotation owb = ((Annotation) wordBlocks.get(w-1));
				Annotation iwb = ((Annotation) wordBlocks.get(w));
				if (AnnotationUtils.liesIn(iwb, owb))
					wordBlocks.remove(w--);
			}
			
			//	get blocks in brackets (and double quotes, too) as a whole
			Annotation[] bracketBlocks = this.getBracketBlocks(bibRef, bibRef.wordBlockExcluded);
			
			//	sort out plain word blocks covered by ones in brackets
			for (int w = 0; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w));
				for (int b = 0; b < bracketBlocks.length; b++)
					if (AnnotationUtils.overlaps(wb, bracketBlocks[b])) {
						wb = null;
						break;
					}
				if (wb == null)
					wordBlocks.remove(w--);
			}
			
			//	add blocks in brackets
			wordBlocks.addAll(Arrays.asList(bracketBlocks));
			Collections.sort(wordBlocks);
			
			//	merge immediately adjacent blocks, and ones with exactly one punctuation mark in between that is very rare as a field separator
			for (int w = 1; w < wordBlocks.size(); w++) {
				Annotation wb = ((Annotation) wordBlocks.get(w-1));
				Annotation lwb = ((Annotation) wordBlocks.get(w));
				boolean merge = false;
				if (lwb.getStartIndex() <= wb.getEndIndex())
					merge = true;
				else if (((lwb.getStartIndex() - wb.getEndIndex()) == 1) && (":&+/".indexOf(bibRef.annotation.valueAt(wb.getEndIndex())) != -1))
					merge = true;
				if (merge) {
					Annotation mwb = Gamta.newAnnotation(bibRef.annotation, null, wb.getStartIndex(), (lwb.getEndIndex() - wb.getStartIndex()));
					wordBlocks.set((w-1), mwb);
					wordBlocks.remove(w--);
				}
			}
		}
		
		//	sort and return what we have
		Collections.sort(wordBlocks);
		bibRef.wordBlocks = ((Annotation[]) wordBlocks.toArray(new Annotation[wordBlocks.size()]));
	}
	
	private Annotation[] getBracketBlocks(BibRef bibRef, boolean[] isNonTitle) {
		if (DEBUG) System.out.println("Getting bracketed / quoted blocks from " + bibRef.annotation.toXML());
		
		//	find blocks in brackets
		Annotation[] bracketBlocks;
		ArrayList bracketBlockList = new ArrayList();
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\([A-Za-z1-9][^\\)]+\\)", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\[[A-Za-z1-9][^\\]]+\\]", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\{[A-Za-z1-9][^\\}]+\\}", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = Gamta.extractAllMatches(bibRef.annotation, "\\\"[A-Za-z1-9][^\\\"]+\\\"", true, true, true);
		bracketBlockList.addAll(Arrays.asList(bracketBlocks));
		bracketBlocks = ((Annotation[]) bracketBlockList.toArray(new Annotation[bracketBlockList.size()]));
		bracketBlockList.clear();
		Arrays.sort(bracketBlocks);
		
		//	filter out blocks already assigned
		for (int b = 0; b < bracketBlocks.length; b++) {
			if (DEBUG) System.out.println(" - investigating " + bracketBlocks[b].getValue());
			for (int t = bracketBlocks[b].getStartIndex(); t < bracketBlocks[b].getEndIndex(); t++)
				if (isNonTitle[t]) {
					if (DEBUG) System.out.println("   - interfers with pre-classified token (" + bibRef.structure.details[t] + ") " + bibRef.annotation.valueAt(t));
					bracketBlocks[b] = null;
					break;
				}
			if (bracketBlocks[b] != null) {
				bracketBlockList.add(bracketBlocks[b]);
				if (DEBUG) System.out.println("   ==> retained");
			}
			else if (DEBUG) System.out.println("   ==> discarded");
		}
		if (bracketBlockList.size() < bracketBlocks.length)
			bracketBlocks = ((Annotation[]) bracketBlockList.toArray(new Annotation[bracketBlockList.size()]));
		bracketBlockList.clear();
		
		//	filter out blocks that are included in others
		for (int b = 0; b < bracketBlocks.length; b++) {
			if (bracketBlockList.isEmpty() || !AnnotationUtils.liesIn(bracketBlocks[b], ((Annotation) bracketBlockList.get(bracketBlockList.size()-1))))
				bracketBlockList.add(bracketBlocks[b]);
		}
		
		//	finally ...
		return ((Annotation[]) bracketBlockList.toArray(new Annotation[bracketBlockList.size()]));
	}
	
	private Annotation[] getTitleCaseAbbreviationBlocks(Annotation bibRef, boolean[] isNonTitle) {
		
		//	find abbreviated blocks
		Annotation[] abbreviationBlocks = Gamta.extractAllMatches(bibRef, this.titleCaseAbbreviationBlockRegEx, true, true, false);
		ArrayList abbreviationBlockList = new ArrayList();
		
		//	filter out blocks already assigned
		for (int a = 0; a < abbreviationBlocks.length; a++) {
			for (int t = abbreviationBlocks[a].getStartIndex(); t < abbreviationBlocks[a].getEndIndex(); t++)
				if (isNonTitle[t]) {
					abbreviationBlocks[a] = null;
					break;
				}
			if (abbreviationBlocks[a] != null)
				abbreviationBlockList.add(abbreviationBlocks[a]);
		}
		abbreviationBlocks = ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
		abbreviationBlockList.clear();
		
		//	filter out blocks that do not start right after a punctuation mark
		for (int a = 0; a < abbreviationBlocks.length; a++) {
			if ((abbreviationBlocks[a].getStartIndex() != 0) && Gamta.isPunctuation(bibRef.valueAt(abbreviationBlocks[a].getStartIndex()-1)))
				abbreviationBlockList.add(abbreviationBlocks[a]);
		}
		abbreviationBlocks = ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
		abbreviationBlockList.clear();
		
		//	filter out blocks that include word with more than three vowels
		for (int a = 0; a < abbreviationBlocks.length; a++) {
			int maxVowelCount = 0;
			for (int t = 0; t < abbreviationBlocks[a].size(); t++) {
				int vowelCount = 0;
				String v = abbreviationBlocks[a].valueAt(t);
				for (int c = 0; c < v.length(); c++) {
					if ("AEIOUYaeiouy".indexOf(v.charAt(c)) != -1)
						vowelCount++;
				}
				maxVowelCount = Math.max(maxVowelCount, vowelCount);
			}
			if (maxVowelCount <= 3)
				abbreviationBlockList.add(abbreviationBlocks[a]);
		}
		abbreviationBlocks = ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
		abbreviationBlockList.clear();
		
		//	filter out blocks that are included in others
		for (int a = 0; a < abbreviationBlocks.length; a++) {
			if (abbreviationBlockList.isEmpty() || !AnnotationUtils.overlaps(abbreviationBlocks[a], ((Annotation) abbreviationBlockList.get(abbreviationBlockList.size()-1))))
				abbreviationBlockList.add(abbreviationBlocks[a]);
		}
		
		//	finally ...
		return ((Annotation[]) abbreviationBlockList.toArray(new Annotation[abbreviationBlockList.size()]));
	}
	
	private void processVolumeRefs(BibRef[] bibRefs, AuthorListStyle authorListStyle) {
		ArrayList volumeRefList = new ArrayList();
//		HashMap refsToVolumeRefs = new HashMap();
		for (int r = 0; r < bibRefs.length; r++) {
			MutableAnnotation volumeRef = null;
			MutableAnnotation[] volumeRefs = bibRefs[r].annotation.getMutableAnnotations(VOLUME_REFERENCE_ANNOTATION_TYPE);
			if ((volumeRefs.length != 0) && (volumeRefs[0].size() < bibRefs[r].annotation.size()))
				volumeRef = volumeRefs[0];
			if ((volumeRef == null) && (bibRefs[r].volumeReference != null))
				volumeRef = bibRefs[r].annotation.addAnnotation(bibRefs[r].volumeReference);
			if (volumeRef != null) {
//				String bibRefParagraphID = bibRefParagraphIDs.getProperty(bibRefs[r].annotation.getAnnotationID());
//				if (bibRefParagraphID != null)
//					bibRefParagraphIDs.setProperty(volumeRef.getAnnotationID(), bibRefParagraphID);
				Object pageId = bibRefs[r].annotation.getAttribute(PAGE_ID_ATTRIBUTE);
				if (pageId != null)
					volumeRef.setAttribute(PAGE_ID_ATTRIBUTE, pageId);
				Object pageNumber = bibRefs[r].annotation.getAttribute(PAGE_NUMBER_ATTRIBUTE);
				if (pageNumber != null)
					volumeRef.setAttribute(PAGE_NUMBER_ATTRIBUTE, pageNumber);
				
				bibRefs[r].volumeRef = new BibRef(volumeRef);
				bibRefs[r].volumeRef.parentRef = bibRefs[r];
				volumeRefList.add(bibRefs[r].volumeRef);
//				refsToVolumeRefs.put(bibRefs[r].annotation.getAnnotationID(), volumeRef);
//				
//				Annotation[] journalOrPublisher = bibRefs[r].annotation.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
//				if ((journalOrPublisher.length != 0) && !AnnotationUtils.overlaps(volumeRef, journalOrPublisher[0]))
//					volumeRef.setAttribute("externalOrigin", "true");
			}
		}
		
		if (volumeRefList.size() == 0)
			return;
		
//		MutableAnnotation[] volumeRefs = ((MutableAnnotation[]) volumeRefList.toArray(new MutableAnnotation[volumeRefList.size()]));
//		this.parseBibRefs(volumeRefs, authorListStyle);
		BibRef[] volumeRefs = ((BibRef[]) volumeRefList.toArray(new BibRef[volumeRefList.size()]));
		this.parseBibRefs(volumeRefs, authorListStyle);
		
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].volumeRef == null)
				continue;
			
			//	transfer editors
			if (bibRefs[r].volumeRef.authors != null) {
				bibRefs[r].editors = new Annotation[bibRefs[r].volumeRef.authors.length];
				for (int a = 0; a < bibRefs[r].volumeRef.authors.length; a++)
					bibRefs[r].editors[a] = Gamta.newAnnotation(bibRefs[r].annotation, EDITOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.authors[a].getStartIndex()), bibRefs[r].volumeRef.authors[a].size());
			}
			
			//	transfer volume designators ...
			if (bibRefs[r].volumeRef.volumeDesignators != null) {
				bibRefs[r].volumeDesignators = new Annotation[bibRefs[r].volumeRef.volumeDesignators.length];
				for (int v = 0; v < bibRefs[r].volumeRef.volumeDesignators.length; v++) {
					bibRefs[r].volumeDesignators[v] = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.volumeDesignators[v].getStartIndex()), bibRefs[r].volumeRef.volumeDesignators[v].size());
					bibRefs[r].volumeDesignators[v].setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
				}
			}
			if (bibRefs[r].volumeRef.volumeDesignator != null) {
				bibRefs[r].volumeDesignator = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.volumeDesignator.getStartIndex()), bibRefs[r].volumeRef.volumeDesignator.size());
				bibRefs[r].volumeDesignator.setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
			}
			
			//	... issue designators ...
			if (bibRefs[r].volumeRef.issueDesignators != null) {
				bibRefs[r].issueDesignators = new Annotation[bibRefs[r].volumeRef.issueDesignators.length];
				for (int i = 0; i < bibRefs[r].volumeRef.issueDesignators.length; i++) {
					bibRefs[r].issueDesignators[i] = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.issueDesignators[i].getStartIndex()), bibRefs[r].volumeRef.issueDesignators[i].size());
					bibRefs[r].issueDesignators[i].setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
				}
			}
			if (bibRefs[r].volumeRef.issueDesignator != null) {
				bibRefs[r].issueDesignator = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.issueDesignator.getStartIndex()), bibRefs[r].volumeRef.issueDesignator.size());
				bibRefs[r].issueDesignator.setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
			}
			
			//	... and number designators
			if (bibRefs[r].volumeRef.numberDesignators != null) {
				bibRefs[r].numberDesignators = new Annotation[bibRefs[r].volumeRef.numberDesignators.length];
				for (int i = 0; i < bibRefs[r].volumeRef.numberDesignators.length; i++) {
					bibRefs[r].numberDesignators[i] = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.numberDesignators[i].getStartIndex()), bibRefs[r].volumeRef.numberDesignators[i].size());
					bibRefs[r].numberDesignators[i].setAttribute(TYPE_ATTRIBUTE, NUMBER_DESIGNATOR_TYPE);
				}
			}
			if (bibRefs[r].volumeRef.numberDesignator != null) {
				bibRefs[r].numberDesignator = Gamta.newAnnotation(bibRefs[r].annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (bibRefs[r].volumeRef.annotation.getStartIndex() + bibRefs[r].volumeRef.numberDesignator.getStartIndex()), bibRefs[r].volumeRef.numberDesignator.size());
				bibRefs[r].numberDesignator.setAttribute(TYPE_ATTRIBUTE, NUMBER_DESIGNATOR_TYPE);
			}
			
			//	transfer structural details
			for (int s = 0; s < bibRefs[r].volumeRef.structure.details.length; s++) {
				if (AUTHOR_LIST_ANNOTATION_TYPE.equals(bibRefs[r].volumeRef.structure.details[s]))
					bibRefs[r].structure.details[s + bibRefs[r].volumeRef.annotation.getStartIndex()] = EDITOR_LIST_ANNOTATION_TYPE;
				else bibRefs[r].structure.details[s + bibRefs[r].volumeRef.annotation.getStartIndex()] = bibRefs[r].volumeRef.structure.details[s];
			}
			
		}
//		for (int c = 0; c < volumeRefs.length; c++) {
//			AnnotationFilter.renameAnnotations(volumeRefs[c], AUTHOR_ANNOTATION_TYPE, EDITOR_ANNOTATION_TYPE);
//			AnnotationFilter.renameAnnotations(volumeRefs[c], TITLE_ANNOTATION_TYPE, VOLUME_TITLE_ANNOTATION_TYPE);
//			AnnotationFilter.removeAnnotations(volumeRefs[c], PAGINATION_ANNOTATION_TYPE);
//		}
//		
//		for (int r = 0; r < bibRefs.length; r++) {
//			MutableAnnotation volumeRef = ((MutableAnnotation) refsToVolumeRefs.get(bibRefs[r].annotation.getAnnotationID()));
//			if (volumeRef == null)
//				continue;
//			Annotation[] journalOrPublisher = bibRefs[r].annotation.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
//			if (journalOrPublisher.length != 0)
//				bibRefs[r].journalOrPublisher = journalOrPublisher[0];
//		}
//		
//		AnnotationFilter.removeAnnotations(data, VOLUME_REFERENCE_ANNOTATION_TYPE);
	}
	
//	private void processVolumeRefs(MutableAnnotation data, BibRef[] bibRefs, AuthorListStyle authorListStyle, Properties parameters) {
//		ArrayList volumeRefList = new ArrayList();
//		HashMap refsToVolumeRefs = new HashMap();
//		for (int r = 0; r < bibRefs.length; r++) {
//			MutableAnnotation volumeRef = null;
//			MutableAnnotation[] volumeRefs = bibRefs[r].annotation.getMutableAnnotations(VOLUME_REFERENCE_ANNOTATION_TYPE);
//			if ((volumeRefs.length != 0) && (volumeRefs[0].size() < bibRefs[r].annotation.size()))
//				volumeRef = volumeRefs[0];
//			if ((volumeRef == null) && (bibRefs[r].volumeReference != null))
//				volumeRef = bibRefs[r].annotation.addAnnotation(bibRefs[r].volumeReference);
//			if (volumeRef != null) {
////				String bibRefParagraphID = bibRefParagraphIDs.getProperty(bibRefs[r].annotation.getAnnotationID());
////				if (bibRefParagraphID != null)
////					bibRefParagraphIDs.setProperty(volumeRef.getAnnotationID(), bibRefParagraphID);
//				Object pageId = bibRefs[r].annotation.getAttribute(PAGE_ID_ATTRIBUTE);
//				if (pageId != null)
//					volumeRef.setAttribute(PAGE_ID_ATTRIBUTE, pageId);
//				Object pageNumber = bibRefs[r].annotation.getAttribute(PAGE_NUMBER_ATTRIBUTE);
//				if (pageNumber != null)
//					volumeRef.setAttribute(PAGE_NUMBER_ATTRIBUTE, pageNumber);
//				volumeRefList.add(volumeRef);
//				refsToVolumeRefs.put(bibRefs[r].annotation.getAnnotationID(), volumeRef);
//				Annotation[] journalOrPublisher = bibRefs[r].annotation.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
//				if ((journalOrPublisher.length != 0) && !AnnotationUtils.overlaps(volumeRef, journalOrPublisher[0]))
//					volumeRef.setAttribute("externalOrigin", "true");
//			}
//		}
//		
//		if (volumeRefList.size() == 0)
//			return;
//		
//		MutableAnnotation[] volumeRefs = ((MutableAnnotation[]) volumeRefList.toArray(new MutableAnnotation[volumeRefList.size()]));
//		this.parseBibRefs(data, volumeRefs, parameters, authorListStyle);
//		
//		for (int c = 0; c < volumeRefs.length; c++) {
//			AnnotationFilter.renameAnnotations(volumeRefs[c], AUTHOR_ANNOTATION_TYPE, EDITOR_ANNOTATION_TYPE);
//			AnnotationFilter.renameAnnotations(volumeRefs[c], TITLE_ANNOTATION_TYPE, VOLUME_TITLE_ANNOTATION_TYPE);
//			AnnotationFilter.removeAnnotations(volumeRefs[c], PAGINATION_ANNOTATION_TYPE);
//		}
//		
//		for (int r = 0; r < bibRefs.length; r++) {
//			MutableAnnotation volumeRef = ((MutableAnnotation) refsToVolumeRefs.get(bibRefs[r].annotation.getAnnotationID()));
//			if (volumeRef == null)
//				continue;
//			Annotation[] journalOrPublisher = bibRefs[r].annotation.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
//			if (journalOrPublisher.length != 0)
//				bibRefs[r].journalOrPublisher = journalOrPublisher[0];
//		}
//		
//		AnnotationFilter.removeAnnotations(data, VOLUME_REFERENCE_ANNOTATION_TYPE);
//	}
//	
	private void getBaseDetails(BibRef bibRef) {
		
		//	this one's been parsed before, use existing annotations
		if (bibRef.preExistingStructure) {
			
			//	- year (four digit number between 1500 and 2100)
			bibRef.years = bibRef.annotation.getAnnotations(YEAR_ANNOTATION_TYPE);
			
			//	- author names (try "Initials LastName", "LastName, Initials", "FirstName LastName", and "LastName, FirstName", then choose the pattern with most matches; if no match found in some reference(s), try "LastName" as well)
			bibRef.authorNames = bibRef.annotation.getAnnotations(AUTHOR_ANNOTATION_TYPE);
			
			//	- page ranges ("pp." or "pages" followed by "Number - Number", or "p." or "page" followed by a number)
			bibRef.pageRanges = bibRef.annotation.getAnnotations(PAGINATION_ANNOTATION_TYPE);
			
			//	- page numbers ("p." or "page" followed by a number)
			bibRef.pageNumbers = new Annotation[0];
			
			//	- volume/issue numbers ("no.", "vol.", etc. followed by a number)
			bibRef.partDesignators = bibRef.annotation.getAnnotations(PART_DESIGNATOR_ANNOTATION_TYPE);
			
			//	classify part designators
			this.classifyPartDesignators(bibRef);
			
			//	... and we're done here
			return;
		}
		
		//	this one's new
		if (DEBUG) System.out.println("Parsing bibliographic reference " + bibRef.annotation.toXML());
		
		//	- year (four digit number between 1500 and 2100)
		bibRef.years = (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRef.annotation.getType()) ? new Annotation[0] : this.getYears(bibRef));
		
		//	- author names (try "Initials LastName", "LastName, Initials", "FirstName LastName", and "LastName, FirstName", then choose the pattern with most matches; if no match found in some reference(s), try "LastName" as well)
		bibRef.authorNames = this.getAuthorNames(bibRef.annotation);
		
		//	- page ranges ("pp." or "pages" followed by "Number - Number", or "p." or "page" followed by a number)
		bibRef.pageRanges = (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRef.annotation.getType()) ? new Annotation[0] : this.getPageRanges(bibRef));
		
		//	- page numbers ("p." or "page" followed by a number)
		bibRef.pageNumbers = (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRef.annotation.getType()) ? new Annotation[0] : this.getPageNumbers(bibRef));
		
		//	- volume/issue numbers ("no.", "vol.", etc. followed by a number)
		bibRef.partDesignators = this.getPartDesignators(bibRef);
		
		//	forget about page numbers and part designators if there are book content infos and no page ranges (if page range present along with part designators, we have a rare mixture ...)
		if ((bibRef.bookContentInfos.size() != 0) && (bibRef.pageRanges.length == 0)) {
			bibRef.pageNumbers = new Annotation[0];
			bibRef.partDesignators = new Annotation[0];
		}
		
		//	classify part desigantors
		this.classifyPartDesignators(bibRef);
		
		//	sort out page numbers, years, and volume numbers located inside page ranges
		ArrayList prCleanupList = new ArrayList();
		int prIndex = 0;
		
		//	years
		prCleanupList.clear();
		prIndex = 0;
		for (int cl = 0; cl < bibRef.years.length; cl++) {
			while ((prIndex < bibRef.pageRanges.length) && (bibRef.pageRanges[prIndex].getEndIndex() <= bibRef.years[cl].getStartIndex()))
				prIndex++;
			if ((prIndex == bibRef.pageRanges.length) || !AnnotationUtils.liesIn(bibRef.years[cl], bibRef.pageRanges[prIndex]))
				prCleanupList.add(bibRef.years[cl]);
		}
		if (prCleanupList.size() != 0) // if we have a year range and no page ranges, this prevents mixups
			bibRef.years = ((Annotation[]) prCleanupList.toArray(new Annotation[prCleanupList.size()]));
		
		//	page numbers
		prCleanupList.clear();
		prIndex = 0;
		for (int cl = 0; cl < bibRef.pageNumbers.length; cl++) {
			if (bibRef.partDesignatorHints.containsKey(new Integer(bibRef.pageNumbers[cl].getStartIndex())))
				continue;
			while ((prIndex < bibRef.pageRanges.length) && (bibRef.pageRanges[prIndex].getEndIndex() <= bibRef.pageNumbers[cl].getStartIndex()))
				prIndex++;
			if ((prIndex == bibRef.pageRanges.length) || !AnnotationUtils.liesIn(bibRef.pageNumbers[cl], bibRef.pageRanges[prIndex]))
				prCleanupList.add(bibRef.pageNumbers[cl]);
		}
		bibRef.pageNumbers = ((Annotation[]) prCleanupList.toArray(new Annotation[prCleanupList.size()]));
		
		//	part designators
		prCleanupList.clear();
		prIndex = 0;
		for (int cl = 0; cl < bibRef.partDesignators.length; cl++) {
			while ((prIndex < bibRef.pageRanges.length) && (bibRef.pageRanges[prIndex].getEndIndex() <= bibRef.partDesignators[cl].getStartIndex()))
				prIndex++;
			if ((prIndex == bibRef.pageRanges.length) || !AnnotationUtils.liesIn(bibRef.partDesignators[cl], bibRef.pageRanges[prIndex]))
				prCleanupList.add(bibRef.partDesignators[cl]);
		}
		
		bibRef.partDesignators = ((Annotation[]) prCleanupList.toArray(new Annotation[prCleanupList.size()]));
		
		//	sort part designators
		ArrayList volumeDesignators = new ArrayList();
		ArrayList issueDesignators = new ArrayList();
		ArrayList numberDesignators = new ArrayList();
		ArrayList fascicleDesignators = new ArrayList();
		ArrayList seriesDesignators = new ArrayList();
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			String partDesignatorType = ((String) bibRef.partDesignators[p].getAttribute(TYPE_ATTRIBUTE));
			if (VOLUME_DESIGNATOR_TYPE.equals(partDesignatorType))
				volumeDesignators.add(bibRef.partDesignators[p]);
			else if (ISSUE_DESIGNATOR_TYPE.equals(partDesignatorType))
				issueDesignators.add(bibRef.partDesignators[p]);
			else if (NUMBER_DESIGNATOR_TYPE.equals(partDesignatorType))
				numberDesignators.add(bibRef.partDesignators[p]);
			else if (FASCICLE_DESIGNATOR_TYPE.equals(partDesignatorType))
				fascicleDesignators.add(bibRef.partDesignators[p]);
			else if (SERIES_DESIGNATOR_TYPE.equals(partDesignatorType))
				seriesDesignators.add(bibRef.partDesignators[p]);
//			else System.out.println("Unassignable part designator: " + bibRef.partDesignators[p].toXML());
		}
		bibRef.volumeDesignators = ((Annotation[]) volumeDesignators.toArray(new Annotation[volumeDesignators.size()]));
		bibRef.issueDesignators = ((Annotation[]) issueDesignators.toArray(new Annotation[issueDesignators.size()]));
		bibRef.numberDesignators = ((Annotation[]) numberDesignators.toArray(new Annotation[numberDesignators.size()]));
		bibRef.fascicleDesignators = ((Annotation[]) fascicleDesignators.toArray(new Annotation[fascicleDesignators.size()]));
		bibRef.seriesDesignators = ((Annotation[]) seriesDesignators.toArray(new Annotation[seriesDesignators.size()]));
	}
	
	private void getStructures(BibRef bibRef) {
		
		//	wrap author lists
		Annotation[] authorLists;
		if (bibRef.preExistingStructure) {
			authorLists = new Annotation[1];
			authorLists[0] = bibRef.authorList;
		}
		else {
			authorLists = new Annotation[bibRef.authorLists.length];
			for (int l = 0; l < bibRef.authorLists.length; l++)
				authorLists[l] = bibRef.authorLists[l].annotation;
		}
		
		//	check for labeled editor lists
		boolean gotLabeledEditorList = (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRef.annotation.getType()) && (bibRef.authorLists.length != 0) && bibRef.authorLists[0].hasEditorListLabel);
		
		//	use only one of page numbers and page ranges for structure generation (prefer page ranges)
		Annotation[] pageIndicators;
		
		//	got a page range
		if (bibRef.pageRanges.length != 0)
			pageIndicators = bibRef.pageRanges;
		
		//	got a secure page number
		else pageIndicators = bibRef.pageNumbers;
		
		//	TODO_ne figure out if this is (a) more helpful, eg in references to single pages, or (b) more harmful with numbers in references to whole books
		//	==> seems so, at least with URL filter for numbers
		//	unify page indicators
		for (int i = 0; i < pageIndicators.length; i++) {
			pageIndicators[i].changeTypeTo(PAGINATION_ANNOTATION_TYPE);
			pageIndicators[i].setAttribute("type", ((bibRef.pageRanges.length == 0) ? "pageNumber" : "pageRange"));
		}
		
		//	prepare bridging part designator hints
		Annotation[] partDesignators = new Annotation[bibRef.partDesignators.length];
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			Annotation partDesignatorHint = ((Annotation) bibRef.partDesignatorHints.get(new Integer(bibRef.partDesignators[p].getStartIndex())));
			if (partDesignatorHint == null)
				partDesignators[p] = bibRef.partDesignators[p];
			else partDesignators[p] = Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, partDesignatorHint.getStartIndex(), (partDesignatorHint.size() + bibRef.partDesignators[p].size()));
		}
		
		//	generate part designator blocks
		ArrayList partDesignatorBlocks = new ArrayList();
		for (int pdbStart = 0; pdbStart < partDesignators.length; pdbStart++) {
			int pdbEnd = pdbStart;
			
			//	find maximum cohesive block
			for (int l = pdbStart; l < partDesignators.length; l++) {
				
				//	last part designator, has to be block end
				if ((l+1) == partDesignators.length) {
					pdbEnd = l;
					break;
				}
				
				//	next part designator adjacent, block continues
				if (partDesignators[l].getEndIndex() == partDesignators[l+1].getStartIndex())
					continue;
					
				
				//	bridgeable gap to next part designator, block continues
				if (((partDesignators[l].getEndIndex()+1) == partDesignators[l+1].getStartIndex()) && this.partDesignatorBlockSeparators.contains(bibRef.annotation.valueAt(partDesignators[l].getEndIndex())))
					continue;
				
				//	end of block reached
				pdbEnd = l;
				break;
			}
			
			//	add all possible blocks within current maximum block
			for (int s = pdbStart; s <= pdbEnd; s++) {
				if ((partDesignators[s].size() > 1) || Gamta.isNumber(partDesignators[s].firstValue())) // ignore single Roman numbers (all too frequent in the middle of old book titles)
					partDesignatorBlocks.add(partDesignators[s]);
				for (int e = (s+1); e <= pdbEnd; e++)
					partDesignatorBlocks.add(Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, partDesignators[s].getStartIndex(), (partDesignators[e].getEndIndex() - partDesignators[s].getStartIndex())));
			}
			
			//	start over with next unvisited part designator
			pdbStart = pdbEnd;
		}
		
		//	include preceding and following brackets if respective matching bracket included in block
		for (int p = 0; p < partDesignatorBlocks.size(); p++) {
			Annotation partDesignatorBlock = ((Annotation) partDesignatorBlocks.get(p));
			if (partDesignatorBlock.size() == 1)
				continue;
			
			String bracket = null;
			for (int t = 0; t < partDesignatorBlock.size(); t++)
				if (Gamta.isBracket(partDesignatorBlock.valueAt(t))) {
					bracket = partDesignatorBlock.valueAt(t);
					break;
				}
			if (bracket == null)
				continue;
			
			if (Gamta.isOpeningBracket(bracket) && (partDesignatorBlock.getEndIndex() < bibRef.annotation.size()) && Gamta.closes(bibRef.annotation.valueAt(partDesignatorBlock.getEndIndex()), bracket))
				partDesignatorBlock = Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, partDesignatorBlock.getStartIndex(), (partDesignatorBlock.size() + 1));
			else if (Gamta.isClosingBracket(bracket) && (partDesignatorBlock.getStartIndex() != 0) && Gamta.opens(bibRef.annotation.valueAt(partDesignatorBlock.getStartIndex()-1), bracket))
				partDesignatorBlock = Gamta.newAnnotation(bibRef.annotation, PART_DESIGNATOR_ANNOTATION_TYPE, (partDesignatorBlock.getStartIndex()-1), (partDesignatorBlock.size() + 1));
			
			if (partDesignatorBlock != partDesignatorBlocks.get(p))
				partDesignatorBlocks.set(p, partDesignatorBlock);
		}
		
		//	sort part designator blocks so larger ones are preferred in structure vote
		Collections.sort(partDesignatorBlocks);
		
		//	report
		if (DEBUG) {
			System.out.println("Part designator blocks in " + bibRef.annotation.toXML());
			for (int p = 0; p < partDesignatorBlocks.size(); p++)
				System.out.println(((Annotation) partDesignatorBlocks.get(p)).toXML());
		}
		
		//	TODO consider creating blocks out of adjacent years that differ by one
		
		//	set up structure relevant details
		String[] workingStructure = new String[bibRef.annotation.size()];
		Annotation[][] details = {
				authorLists,
				bibRef.years,
				pageIndicators,
				((Annotation[]) partDesignatorBlocks.toArray(new Annotation[partDesignatorBlocks.size()])),
		};
//		Annotation[][] details = {
//				bibRef.authorLists,
//				bibRef.years,
//				pageIndicators,
//				((Annotation[]) partDesignatorBlocks.toArray(new Annotation[partDesignatorBlocks.size()])),
//		};
		boolean[] tryWithoutIfGiven = {
				(!bibRef.preExistingStructure && !gotLabeledEditorList),
				false,
				!bibRef.preExistingStructure,
				!bibRef.preExistingStructure,
			};
		
		//	get structures
		this.getStructures(bibRef, details, 0, tryWithoutIfGiven, workingStructure);
	}
	
	private void getStructures(BibRef bibRef, Annotation[][] details, int detailTypeIndex, boolean[] tryWithoutIfGiven, String[] workingStructure) {
		
		//	we're done here
		if (detailTypeIndex == details.length) {
			bibRef.structures.add(new Structure(bibRef.annotation, workingStructure));
			return;
		}
		
		//	try all options for current detail type
		for (int d = 0; d < details[detailTypeIndex].length; d++) {
			
			//	check if current detail fits
			boolean fits = true;
			for (int s = details[detailTypeIndex][d].getStartIndex(); s < details[detailTypeIndex][d].getEndIndex(); s++)
				fits = (fits && (workingStructure[s] == null));
			
			//	it fits
			if (fits) {
				
				//	put current detail
				for (int s = details[detailTypeIndex][d].getStartIndex(); s < details[detailTypeIndex][d].getEndIndex(); s++)
					workingStructure[s] = details[detailTypeIndex][d].getType();
				
				//	proceed with current detail
				this.getStructures(bibRef, details, (detailTypeIndex+1), tryWithoutIfGiven, workingStructure);
				
				//	clean up
				for (int s = details[detailTypeIndex][d].getStartIndex(); s < details[detailTypeIndex][d].getEndIndex(); s++)
					workingStructure[s] = null;
			}
		}
		
		//	also try proceeding without current detail type (allows for trying out more at the same time)
		if ((details[detailTypeIndex].length == 0) || tryWithoutIfGiven[detailTypeIndex])
			this.getStructures(bibRef, details, (detailTypeIndex+1), tryWithoutIfGiven, workingStructure);
	}
	
//	private void selectStructure(BibRef bibRef, int bibRefCount, StringVector structures, final StringIndex structureCounts, StringVector separators, StringIndex separatorFrequencies, HashMap punctSummaryElementSets, HashMap summaryElementSets, HashMap typeElementSets) {
	private void selectStructure(BibRef bibRef, int bibRefCount, final StringIndex structureCounts, StringVector separators, StringIndex separatorFrequencies, HashMap punctSummaryElementSets, HashMap summaryElementSets, HashMap typeElementSets) {
		if (DEBUG) System.out.println(bibRef.annotation.toXML());
		
		if (false && DEBUG_STRUCTURE_SCORING) {
			Collections.sort(bibRef.structures, new Comparator() {
				public int compare(Object o1, Object o2) {
					Structure s1 = ((Structure) o1);
					Structure s2 = ((Structure) o2);
					return (structureCounts.getCount(s2.punctSummaryString) - structureCounts.getCount(s1.punctSummaryString));
				}
			});
			for (int s = 0; s < bibRef.structures.size(); s++) {
				Structure structure = ((Structure) bibRef.structures.get(s));
				if (DEBUG_STRUCTURE_SCORING) System.out.println("PSS: " + structureCounts.getCount(structure.punctSummaryString) + "/" + bibRefCount + ": " + structure.punctSummaryString);
			}
			
			Collections.sort(bibRef.structures, new Comparator() {
				public int compare(Object o1, Object o2) {
					Structure s1 = ((Structure) o1);
					Structure s2 = ((Structure) o2);
					return (structureCounts.getCount(s2.summaryString) - structureCounts.getCount(s1.summaryString));
				}
			});
			for (int s = 0; s < bibRef.structures.size(); s++) {
				Structure structure = ((Structure) bibRef.structures.get(s));
				if (DEBUG_STRUCTURE_SCORING) System.out.println("SS:  " + structureCounts.getCount(structure.summaryString) + "/" + bibRefCount + ": " + structure.summaryString);
			}
			
			Collections.sort(bibRef.structures, new Comparator() {
				public int compare(Object o1, Object o2) {
					Structure s1 = ((Structure) o1);
					Structure s2 = ((Structure) o2);
					return (structureCounts.getCount(s2.typeString) - structureCounts.getCount(s1.typeString));
				}
			});
			for (int s = 0; s < bibRef.structures.size(); s++) {
				Structure structure = ((Structure) bibRef.structures.get(s));
				if (DEBUG_STRUCTURE_SCORING) System.out.println("TS:  " + structureCounts.getCount(structure.typeString) + "/" + bibRefCount + ": " + structure.typeString);
			}
		}
		
		//	vote structure based on (a) support/frequency and (b) number of detail types covered
		int maxScore = 0;
		Structure maxScoreStructure = null;
		int maxFuzzyScore = 0;
		Structure maxFuzzyScoreStructure = null;
		for (int s = 0; s < bibRef.structures.size(); s++) {
			Structure structure = ((Structure) bibRef.structures.get(s));
			int score = 0;
			
			//	this scoring function seems to work very well !!!
			//	TODOne: experiment with exponents of |detailType| power ==> seems to work very well with square
			int psScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(structure.punctSummaryString));
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.punctSummaryString + " -PSS-> " + psScore);
			score += psScore;
			
			int sScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(structure.summaryString));
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.summaryString + " -SS-> " + sScore);
			score += sScore;
			
			int tScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(structure.typeString));
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.typeString + " -TS-> " + tScore);
			score += tScore;
			
			//	score longes block of '_' (rewards having recognized features close together, thus catch mis-recoginitions in middle of reference)
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -VB-> " + structure.maxVoidBlockLength);
			score += structure.maxVoidBlockLength;
			
			//	score long author lists (overcomes problems when selecting small sub list of long author list voids long block)
			int authorListLength = 0;
			for (int d = 0; d < structure.details.length; d++) {
				if (AUTHOR_LIST_ANNOTATION_TYPE.equals(structure.details[d]))
					authorListLength++;
			}
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -AL-> " + authorListLength);
			score += authorListLength;
			
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" =SCORE=> " + score);
			if (score > maxScore) {
				maxScore = score;
				maxScoreStructure = structure;
//				bibRef.structure = structure;
			}
			else if (score == maxScore) {
				
				//	compare order of part designator and page numbers, and length of author list
				int sPageDataIndex = -1;
				int sPartDesIndex = -1;
				int sAuthorListLength = 0;
				for (int d = 0; d < structure.details.length; d++) {
					if ((sPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(structure.details[d])))
						sPageDataIndex = d;
					else if ((sPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(structure.details[d])))
						sPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(structure.details[d]))
						sAuthorListLength++;
				}
				int mssPageDataIndex = -1;
				int mssPartDesIndex = -1;
				int mssAuthorListLength = 0;
				for (int d = 0; d < maxScoreStructure.details.length; d++) {
					if ((mssPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(maxScoreStructure.details[d])))
						mssPageDataIndex = d;
					else if ((mssPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(maxScoreStructure.details[d])))
						mssPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(maxScoreStructure.details[d]))
						mssAuthorListLength++;
				}
				
				//	prefer part designator left of page number
				if ((mssPageDataIndex != -1) && (sPageDataIndex > mssPageDataIndex) && (sPartDesIndex != -1) && (sPartDesIndex < mssPartDesIndex))
					maxScoreStructure = structure;
				
				//	prefer longer author list
				else if (sAuthorListLength > mssAuthorListLength)
					maxScoreStructure = structure;
			}
			
			//	use structure subsumption
			int fuzzyScore = 0;
			
			//	compare punctuated summary
//			System.out.println(" - " + structure.punctSummaryString + " vs.:");
			LinkedHashSet sPunctSummaryElements = ((LinkedHashSet) punctSummaryElementSets.get(structure.punctSummaryString));
			int psFuzzyScore = getFuzzyScore(structure.detailTypes.size(), structure.punctSummaryString, sPunctSummaryElements, structureCounts, punctSummaryElementSets);
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.punctSummaryString + " -PSS-F-> " + psFuzzyScore);
			fuzzyScore += psFuzzyScore;
			
			//	compare summary
//			System.out.println(" - " + structure.summaryString + " vs.:");
			LinkedHashSet sSummaryElements = ((LinkedHashSet) summaryElementSets.get(structure.summaryString));
			int sFuzzyScore = getFuzzyScore(structure.detailTypes.size(), structure.summaryString, sSummaryElements, structureCounts, summaryElementSets);
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.summaryString + " -SS-F-> " + sFuzzyScore);
			fuzzyScore += sFuzzyScore;
			
			//	compare types
//			System.out.println(" - " + structure.typeString + " vs.:");
			LinkedHashSet sTypeElements = ((LinkedHashSet) typeElementSets.get(structure.typeString));
			int tFuzzyScore = getFuzzyScore(structure.detailTypes.size(), structure.typeString, sTypeElements, structureCounts, typeElementSets);
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" - " + structure.typeString + " -TS-F-> " + tFuzzyScore);
			fuzzyScore += tFuzzyScore;
			
			//	score longes block of '_' (rewards having recognized features close together, thus catch mis-recoginitions in middle of reference)
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -VB-F-> " + structure.maxVoidBlockLength);
			fuzzyScore += structure.maxVoidBlockLength;
			
			//	score long author lists (overcomes problems when selecting small sub list of long author list voids long block)
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" -AL-F-> " + authorListLength);
			fuzzyScore += authorListLength;
			
			//	got a new leader?
			if (DEBUG_STRUCTURE_SCORING) System.out.println(" =SCORE-F=> " + fuzzyScore);
			if (fuzzyScore > maxFuzzyScore) {
				maxFuzzyScore = fuzzyScore;
				maxFuzzyScoreStructure = structure;
			}
			else if (fuzzyScore == maxFuzzyScore) {
				
				//	compare order or part designator and page numbers
				int sPageDataIndex = -1;
				int sPartDesIndex = -1;
				int sAuthorListLength = 0;
				for (int d = 0; d < structure.details.length; d++) {
					if ((sPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(structure.details[d])))
						sPageDataIndex = d;
					else if ((sPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(structure.details[d])))
						sPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(structure.details[d]))
						sAuthorListLength++;
				}
				int mssPageDataIndex = -1;
				int mssPartDesIndex = -1;
				int mssAuthorListLength = 0;
				for (int d = 0; d < maxFuzzyScoreStructure.details.length; d++) {
					if ((mssPageDataIndex == -1 && PAGINATION_ANNOTATION_TYPE.equals(maxFuzzyScoreStructure.details[d])))
						mssPageDataIndex = d;
					else if ((mssPartDesIndex == -1 && PART_DESIGNATOR_ANNOTATION_TYPE.equals(maxFuzzyScoreStructure.details[d])))
						mssPartDesIndex = d;
					else if (AUTHOR_LIST_ANNOTATION_TYPE.equals(maxFuzzyScoreStructure.details[d]))
						mssAuthorListLength++;
				}
				
				//	prefer part designator left of page number
				if ((mssPageDataIndex != -1) && (sPageDataIndex > mssPageDataIndex) && (sPartDesIndex != -1) && (sPartDesIndex < mssPartDesIndex))
					maxFuzzyScoreStructure = structure;
				
				//	prefer longer author list
				else if (sAuthorListLength > mssAuthorListLength)
					maxFuzzyScoreStructure = structure;
			}
		}
		
		//	assign structure
//		bibRef.structure = maxScoreStructure;
		bibRef.structure = maxFuzzyScoreStructure;
		
		if (bibRef.structure == null) {
			String[] dummyWorkingStructure = new String[bibRef.annotation.size()];
			for (int s = 0; s < dummyWorkingStructure.length; s++)
				dummyWorkingStructure[s] = "_";
			bibRef.structure = new Structure(bibRef.annotation, dummyWorkingStructure);
		}
		
		if (DEBUG) {
			System.out.println(" =plain=> (" + maxScore + ") " + ((maxScoreStructure == null) ? "not found" : maxScoreStructure.punctSummaryString));
			System.out.println(" =fuzzy=> (" + maxFuzzyScore + ") " + ((maxFuzzyScoreStructure == null) ? "not found" : maxFuzzyScoreStructure.punctSummaryString));
			System.out.println("   ==> (" + maxFuzzyScore + ") " + bibRef.structure.punctSummaryString);
		}
		
		//	count frequencies of separator chars
		for (int s = 1; s < (bibRef.structure.punctSummary.length - 1); s++)
			if (Gamta.isPunctuation(bibRef.structure.punctSummary[s])
				&&
				!"_".equals(bibRef.structure.punctSummary[s])
				&&
				(
					Gamta.isWord(bibRef.structure.punctSummary[s-1])
					||
					Gamta.isWord(bibRef.structure.punctSummary[s+1])
				)) {
				separators.addElementIgnoreDuplicates(bibRef.structure.punctSummary[s]);
				separatorFrequencies.add(bibRef.structure.punctSummary[s]);
			}
		
		//	this one's been parsed before, no annotation to add
		if (bibRef.preExistingStructure)
			return;
		
		//	transform years into annotations (have to do this first so we can get proceedings titles)
		for (int d = 0; d < bibRef.structure.details.length; d++)
			if (YEAR_ANNOTATION_TYPE.equals(bibRef.structure.details[d])) {
				Annotation detail = Gamta.newAnnotation(bibRef.annotation, bibRef.structure.details[d], d, 1);
				if (YEAR_ANNOTATION_TYPE.equals(bibRef.structure.details[d]))
					bibRef.year = detail;
			}
		
		//	get proceedings titles, and remove any part designators they span, also cleaning structure
		Annotation[] proceedingsTitles = this.getProceedingsTitles(bibRef);
		if (proceedingsTitles.length != 0) {
			for (int pt = 0; pt < proceedingsTitles.length; pt++) {
				for (int t = proceedingsTitles[pt].getStartIndex(); t < proceedingsTitles[pt].getEndIndex(); t++)
					bibRef.structure.details[t] = "_";
			}
			bibRef.structure = new Structure(bibRef.annotation, bibRef.structure.details);
		}
		
		//	transform details into annotations
		for (int d = 0; d < bibRef.structure.details.length; d++) {
			if ("_".equals(bibRef.structure.details[d]))
				continue;
			
			int e = (d+1);
			while ((e < bibRef.structure.details.length) && bibRef.structure.details[d].equals(bibRef.structure.details[e]))
				e++;
			Annotation detail = Gamta.newAnnotation(bibRef.annotation, bibRef.structure.details[d], d, (e-d));
			if (AUTHOR_LIST_ANNOTATION_TYPE.equals(bibRef.structure.details[d])) {
				ArrayList authors = null;
				AuthorList authorList = null;
				for (int l = 0; l < bibRef.authorLists.length; l++) {
					if (!AnnotationUtils.equals(detail, bibRef.authorLists[l].annotation, false))
						continue;
					if ((authorList == null) || (bibRef.authorLists[l].bridged.size() < authorList.bridged.size()))
						authorList = bibRef.authorLists[l];
				}
				if (authorList != null) {
					bibRef.authorList = authorList.annotation;
					authors = new ArrayList(authorList.authorNames);
				}
				if (bibRef.authorList == null) {
					bibRef.authorList = detail;
					authors = new ArrayList();
					int authorEnd = -1;
					for (int a = 0; a < bibRef.authorNames.length; a++) {
						if (bibRef.authorNames[a].getStartIndex() <= authorEnd)
							continue;
						if (AnnotationUtils.liesIn(bibRef.authorNames[a], bibRef.authorList)) {
							authors.add(bibRef.authorNames[a]);
							authorEnd = bibRef.authorNames[a].getEndIndex();
						}
					}
				}
				if (authors.size() != 0) {
					Annotation lastAuthor = ((Annotation) authors.get(authors.size() -1));
					if (etAlSpecialType.equals(lastAuthor.getType()))
						authors.remove(authors.size() -1);
				}
				bibRef.authors = ((Annotation[]) authors.toArray(new Annotation[authors.size()]));
			}
			else if (PAGINATION_ANNOTATION_TYPE.equals(bibRef.structure.details[d]) || PAGE_RANGE_ANNOTATION_TYPE.equals(bibRef.structure.details[d]) || PAGE_NUMBER_TYPE.equals(bibRef.structure.details[d])) {
				if (!VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRef.annotation.getType()))
					bibRef.pagination = detail;
			}
			else if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(bibRef.structure.details[d])) {
				//	go through part designators and assign respectively
				for (int p = 0; p < bibRef.partDesignators.length; p++) {
					if (!AnnotationUtils.contains(detail, bibRef.partDesignators[p])) {
						System.out.println("Out-of-place part designator: " + bibRef.partDesignators[p].toXML());
						continue;
					}
					String partDesignatorType = ((String) bibRef.partDesignators[p].getAttribute(TYPE_ATTRIBUTE));
					if (VOLUME_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.volumeDesignator = bibRef.partDesignators[p];
					else if (ISSUE_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.issueDesignator = bibRef.partDesignators[p];
					else if (NUMBER_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.numberDesignator = bibRef.partDesignators[p];
					else if (FASCICLE_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.fascicleDesignator = bibRef.partDesignators[p];
					else if (SERIES_DESIGNATOR_TYPE.equals(partDesignatorType))
						bibRef.seriesDesignator = bibRef.partDesignators[p];
					else System.out.println("Unclassified part designator: " + bibRef.partDesignators[p].toXML());
				}
			}
			d = (e-1); // proceed at e, mind countering loop increment, though
		}
		
		if (DEBUG) {
			System.out.println("authorList: " + ((bibRef.authorList == null) ? "" : bibRef.authorList.getValue()));
			System.out.println("year: " + ((bibRef.year == null) ? "" : bibRef.year.getValue()));
			System.out.println("volume: " + ((bibRef.volumeDesignator == null) ? "" : bibRef.volumeDesignator.getValue()));
			System.out.println("issue: " + ((bibRef.issueDesignator == null) ? "" : bibRef.issueDesignator.getValue()));
			System.out.println("number: " + ((bibRef.numberDesignator == null) ? "" : bibRef.numberDesignator.getValue()));
			System.out.println("series: " + ((bibRef.seriesDesignator == null) ? "" : bibRef.seriesDesignator.getValue()));
			System.out.println("fascicle: " + ((bibRef.fascicleDesignator == null) ? "" : bibRef.fascicleDesignator.getValue()));
			System.out.println("page(s): " + ((bibRef.pagination == null) ? "" : bibRef.pagination.getValue()));
			System.out.println();
		}
	}
	
	//	TODOne adjust exponents values SEEMS TO WORK LIKE THIS
	private static final int matchExp = 3;
	private static final int subsumeExp = 2;
	private static final int getFuzzyScore(int sSize, String sString, LinkedHashSet sElements, StringIndex structureCounts, HashMap structureElementSets) {
		int fuzzyScore = 0;
		for (Iterator csit = structureElementSets.keySet().iterator(); csit.hasNext();) {
			String cString = ((String) csit.next());
			int fScore;
			
			//	structures equal, score like above
			if (cString.equals(sString))
//				fScore = (((int) Math.pow(sPunctSummaryElements.size(), 2)) * structureCounts.getCount(structure.typeString));
				fScore = (((int) Math.pow(sSize, matchExp)) * structureCounts.getCount(cString));
			
			//	try subsumption match
			else {
				LinkedHashSet cElements = ((LinkedHashSet) structureElementSets.get(cString));
				if (subsumes(cElements, sElements))
//					fScore = (((int) Math.pow(sSummaryElements.size(), 2)) * structureCounts.getCount(typeString));
//					fScore = (((int) Math.pow(structure.detailTypes.size(), 2)) * structureCounts.getCount(typeString));
					fScore = (((((int) Math.pow(sSize, subsumeExp)) * structureCounts.getCount(cString)) * sElements.size()) / cElements.size());
				else fScore = 0;
			}
			
			//	add score
//			fuzzyScore += fScore;
			fuzzyScore = Math.max(fuzzyScore, fScore);
		}
		
		//	finally ...
		return fuzzyScore;
	}
	
	private static boolean subsumes(LinkedHashSet higherStructure, LinkedHashSet lowerStructure) {
		
		//	lower structure larger than higher structure
		//	==> subsumption match impossible
		if (higherStructure.size() <= lowerStructure.size())
			return false;
		
		//	lower structure has elements not contained in higher structure
		//	==> subsumption match impossible
		if (!higherStructure.containsAll(lowerStructure))
			return false;
		
		//	check element order
		for (Iterator hsit = higherStructure.iterator(), lsit = lowerStructure.iterator(); hsit.hasNext();) {
			
			//	get next element of higher structure
			String hsElement = ((String) hsit.next());
			
			//	element not contained in lower structure
			//	==> ignore it
			if (!lowerStructure.contains(hsElement))
				continue;
			
			//	element contained in lower structure, has to be next in latter to not violate ordering condition
			//	==> if not, higher structure does not subsume lower structure
			if (!lsit.hasNext() || !hsElement.equals(lsit.next()))
				return false;
		}
		
		//	due to containsAll() pre-condition, there cannot be left anything in lower structure
		//	==> we have a subsumption match
		return true;
	}
	
	private void extractVolumeReference(BibRef bibRef, String primarySeparator, AuthorListStyle authorListStyle) {
		
		Annotation[] volumeReferencePrefixes = Gamta.extractAllMatches(bibRef.annotation, "[IiEe][Nn]\\:?", 2);
		if (volumeReferencePrefixes.length == 0)
			return;
		
		Annotation volumeReferencePrefix = null;
		boolean gotEditorStart = false;
		for (int v = 0; v < volumeReferencePrefixes.length; v++) {
			if (DEBUG) System.out.println("Investigating volume reference prefix " + volumeReferencePrefixes[v]);
			if (volumeReferencePrefixes[v].size() == 2) {
				if (DEBUG) System.out.println("==> safe with colon");
				volumeReferencePrefix = volumeReferencePrefixes[v];
				break;
			}
			
			if (volumeReferencePrefixes[v].getStartIndex() < 2)
				continue;
//			if (!primarySeparator.equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1))) {
//				if (DEBUG) System.out.println("==> no preceding separator");
//				continue;
//			}
			if ("\"".equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1))) {
				if (!primarySeparator.equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 2)) && (".,?!".indexOf(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 2)) == -1)) {
					if (DEBUG) System.out.println("==> no preceding separator");
					continue;
				}
			}
			else if (!primarySeparator.equals(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1)) && (".,?!".indexOf(bibRef.annotation.valueAt(volumeReferencePrefixes[v].getStartIndex() - 1)) == -1)) {
				if (DEBUG) System.out.println("==> no preceding separator");
				continue;
			}
			if (bibRef.annotation.size() <= volumeReferencePrefixes[v].getEndIndex())
				continue;
			
			Annotation volumeReferenceCandidate = Gamta.newAnnotation(bibRef.annotation, null, volumeReferencePrefixes[v].getEndIndex(), (bibRef.annotation.size() - volumeReferencePrefixes[v].getEndIndex()));
			Annotation[] editors = this.getAuthorNames(volumeReferenceCandidate);
			Annotation[] editorListLabels = Gamta.extractAllMatches(volumeReferenceCandidate, this.editorListTagRegEx);
			Annotation editor = null;
			for (int e = 0; e < editors.length; e++) {
				if (editors[e].getStartIndex() > 1)
					continue;
				if ((authorListStyle != null) && ((editorListLabels.length == 0) || ((editorListLabels[0].getStartIndex() - editors[e].getEndIndex()) > 4))) {
					String fns = ((String) editors[e].getAttribute(firstNameStyle));
					if (fullNameFNS.equals(fns) && !authorListStyle.firstNameStyles.contains(fns))
						continue;
				}
				if (editors[e].size() > (".".equals(editors[e].lastValue()) ? 2 : 1)) {
					editor = editors[e];
					break;
				}
			}
			if (editor == null) {
				if (DEBUG) System.out.println("==> no editors");
				continue;
			}
			else {
				if (DEBUG) System.out.println("==> found editor name: " + editor);
				volumeReferencePrefix = volumeReferencePrefixes[v];
				gotEditorStart = true;
				break;
			}
		}
		if (volumeReferencePrefix == null)
			return;
		
		int volumeReferenceEnd = bibRef.annotation.size();
		if ((bibRef.pagination != null) && (volumeReferencePrefix.getEndIndex() < bibRef.pagination.getStartIndex())) {
			volumeReferenceEnd = Math.min(volumeReferenceEnd, bibRef.pagination.getStartIndex());
			while ((volumeReferenceEnd > 0) && Gamta.isPunctuation(bibRef.annotation.valueAt(volumeReferenceEnd-1)))
				volumeReferenceEnd--;
		}
		if ((bibRef.year != null) && (volumeReferencePrefix.getEndIndex() < bibRef.year.getStartIndex())) {
			volumeReferenceEnd = Math.min(volumeReferenceEnd, bibRef.year.getStartIndex());
			while ((volumeReferenceEnd > 0) && Gamta.isPunctuation(bibRef.annotation.valueAt(volumeReferenceEnd-1)))
				volumeReferenceEnd--;
		}
		
		if (volumeReferencePrefix.getEndIndex() < volumeReferenceEnd) {
			bibRef.volumeReference = Gamta.newAnnotation(bibRef.annotation, VOLUME_REFERENCE_ANNOTATION_TYPE, volumeReferencePrefix.getEndIndex(), (volumeReferenceEnd - volumeReferencePrefix.getEndIndex()));
			if (gotEditorStart)
				bibRef.volumeReference.setAttribute("editorStart", "true");
			for (int t = -volumeReferencePrefix.size(); t < bibRef.volumeReference.size(); t++)// include 'In'
				bibRef.structure.details[bibRef.volumeReference.getStartIndex() + t] = VOLUME_REFERENCE_ANNOTATION_TYPE;
			if (DEBUG) {
				System.out.println("Got volume reference in " + bibRef.annotation.getValue() + ":");
				System.out.println("  " + bibRef.volumeReference.getValue());
			}
			
			//	clean up part designators located before volume reference
			bibRef.volumeDesignator = this.reSelectPartDesignator(bibRef.annotation, bibRef.volumeDesignators, bibRef.partDesignators, VOLUME_DESIGNATOR_TYPE, bibRef.volumeReference, bibRef.structure.details);
			if (DEBUG) System.out.println("   ==> volume designator set to " + bibRef.volumeDesignator);
			bibRef.issueDesignator = this.reSelectPartDesignator(bibRef.annotation, bibRef.issueDesignators, bibRef.partDesignators, ISSUE_DESIGNATOR_TYPE, bibRef.volumeReference, bibRef.structure.details);
			if (DEBUG) System.out.println("   ==> issue designator set to " + bibRef.issueDesignator);
			bibRef.numberDesignator = this.reSelectPartDesignator(bibRef.annotation, bibRef.numberDesignators, bibRef.partDesignators, NUMBER_DESIGNATOR_TYPE, bibRef.volumeReference, bibRef.structure.details);
			if (DEBUG) System.out.println("   ==> number designator set to " + bibRef.numberDesignator);
		}
	}
	
	private Annotation reSelectPartDesignator(Annotation bibRef, Annotation[] partDesignators, Annotation[] allPartDesignators, String partDesignatorType, Annotation journalOrPublisher, String[] structureDetails) {
		if (partDesignators.length == 0)
			return null;
		
		//	mark part designator tokens
		boolean[] isPartDesignator = new boolean[bibRef.size()];
		Arrays.fill(isPartDesignator, false);
		for (int d = 0; d < allPartDesignators.length; d++) {
			for (int t = allPartDesignators[d].getStartIndex(); t < allPartDesignators[d].getEndIndex(); t++)
				isPartDesignator[t] = true;
		}
		
		//	select first part designator of given type after end of journal / publisher
		Annotation partDesignator = null;
		for (int p = 0; p < partDesignators.length; p++) {
			System.out.println("Assessing " + partDesignators[p].getValue());
			if ((partDesignators[p].getStartIndex() < journalOrPublisher.getEndIndex()) || (partDesignator != null)) {
				System.out.println("  ==> too early, cleaning up");
				for (int d = partDesignators[p].getStartIndex(); d < partDesignators[p].getEndIndex(); d++) {
					if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						structureDetails[d] = "_";
				}
				for (int d = (partDesignators[p].getStartIndex() - 1); d > -1; d--) {
					if (!PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						break;
					if (isPartDesignator[d])
						break;
					structureDetails[d] = "_";
				}
			}
			else if (partDesignator == null) {
				System.out.println("  ==> might fit");
				boolean partDesignatorFits = true;
				for (int d = partDesignators[p].getStartIndex(); d < partDesignators[p].getEndIndex(); d++)
					if (!"_".equals(structureDetails[d]) && !PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d])) {
						partDesignatorFits = false;
						break;
					}
				if (partDesignatorFits) {
					System.out.println("  ==> does fit");
					partDesignator = partDesignators[p];
					for (int d = partDesignator.getStartIndex(); d < partDesignator.getEndIndex(); d++)
						structureDetails[d] = PART_DESIGNATOR_ANNOTATION_TYPE;
				}
				else System.out.println("  ==> interfers with some other number");
			}
		}
		if (partDesignator != null)
			return partDesignator;
		
		//	select first generic part designator after end of journal / publisher
		for (int p = 0; p < allPartDesignators.length; p++) {
			if (!partDesignatorType.equals(allPartDesignators[p].getAttribute(TYPE_ATTRIBUTE, partDesignatorType)))
				continue;
			System.out.println("Assessing " + allPartDesignators[p].getValue());
			if ((allPartDesignators[p].getStartIndex() < journalOrPublisher.getEndIndex()) || (partDesignator != null)) {
				System.out.println("  ==> too early, cleaning up");
				for (int d = allPartDesignators[p].getStartIndex(); d < allPartDesignators[p].getEndIndex(); d++) {
					if (PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						structureDetails[d] = "_";
				}
				for (int d = (allPartDesignators[p].getStartIndex() - 1); d > -1; d--) {
					if (!PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d]))
						break;
					if (isPartDesignator[d])
						break;
					structureDetails[d] = "_";
				}
			}
			else if (partDesignator == null) {
				System.out.println("  ==> might fit");
				boolean partDesignatorFits = true;
				for (int d = allPartDesignators[p].getStartIndex(); d < allPartDesignators[p].getEndIndex(); d++)
					if (!"_".equals(structureDetails[d]) && !PART_DESIGNATOR_ANNOTATION_TYPE.equals(structureDetails[d])) {
						partDesignatorFits = false;
						break;
					}
				if (partDesignatorFits) {
					System.out.println("  ==> does fit");
					partDesignator = allPartDesignators[p];
					partDesignator.setAttribute(TYPE_ATTRIBUTE, partDesignatorType);
					for (int d = partDesignator.getStartIndex(); d < partDesignator.getEndIndex(); d++)
						structureDetails[d] = PART_DESIGNATOR_ANNOTATION_TYPE;
				}
				else System.out.println("  ==> interfers with some other number");
			}
		}
		return partDesignator;
	}
	
	private void parseOrigin(BibRef bibRef, String primarySeparator) {
		if (bibRef.type == null)
			return;
		if (bibRef.journalOrPublisher == null) {
			System.out.println("MISSING ORIGIN IN " + bibRef.annotation.toXML());
			return;
		}
		if (bibRef.preExistingStructure) {
			if (bibRef.type.name.startsWith("journal") && (bibRef.journal != null))
				return;
			else if (bibRef.type.name.startsWith("book") && ((bibRef.publisher != null) || (bibRef.location != null)))
				return;
			else if (bibRef.type.name.startsWith("proceedings") && (bibRef.proceedingsVolumeTitle != null))
				return;
		}
		
		if (bibRef.type.name.startsWith("journal")) {
			bibRef.journal = Gamta.newAnnotation(bibRef.annotation, bibRef.journalOrPublisher);
			bibRef.journal.changeTypeTo(JOURNAL_NAME_ANNOTATION_TYPE);
			return;
		}
		
		if (bibRef.type.name.startsWith("book")) {
			if (!this.parsePublisher(bibRef, bibRef.journalOrPublisher)) {
				//	TODO use lexicons to determine if publisher or location
				//	TODO alternatively, also use number of words (single words become locations)
				bibRef.publisher = Gamta.newAnnotation(bibRef.annotation, bibRef.journalOrPublisher);
				bibRef.publisher.changeTypeTo(PUBLISHER_ANNOTATION_TYPE);
			}
			return;
		}
		
		if (bibRef.type.name.startsWith("proceedings")) {
			//	chunk off volume title, and split rest with publisher parsing heuristics
			int vtSize = 0;
			while ((vtSize < bibRef.journalOrPublisher.size())) {
				String vtValue = bibRef.journalOrPublisher.valueAt(vtSize);
				if (".".equals(vtValue) && !".".equals(primarySeparator)) {
					vtSize++;
					continue;
				}
				if (",.;:".indexOf(vtValue) == -1)
					vtSize++;
				else break;
			}
			if (vtSize < bibRef.journalOrPublisher.size()) {
				bibRef.proceedingsVolumeTitle = Gamta.newAnnotation(bibRef.annotation, PUBLISHER_ANNOTATION_TYPE, bibRef.journalOrPublisher.getStartIndex(), vtSize);
				Annotation location = Gamta.newAnnotation(bibRef.annotation, LOCATION_ANNOTATION_TYPE, (bibRef.journalOrPublisher.getStartIndex() + vtSize + 1), (bibRef.journalOrPublisher.size() - vtSize - 1));
				if (!this.parsePublisher(bibRef, location))
					bibRef.location = location;
			}
			else {
				bibRef.proceedingsVolumeTitle = Gamta.newAnnotation(bibRef.annotation, bibRef.journalOrPublisher);
				bibRef.proceedingsVolumeTitle.changeTypeTo(VOLUME_TITLE_ANNOTATION_TYPE);
			}
			return;
		}
	}
	
	private boolean parsePublisher(BibRef bibRef, Annotation publisher) {
		int split = TokenSequenceUtils.indexOf(bibRef.journalOrPublisher, ":");
		if (split == -1)
			split = TokenSequenceUtils.indexOf(bibRef.journalOrPublisher, ",");
		if (split == -1)
			return false;
		if (":".equals(bibRef.journalOrPublisher.valueAt(split))) {
			bibRef.publisher = Gamta.newAnnotation(bibRef.annotation, PUBLISHER_ANNOTATION_TYPE, (bibRef.journalOrPublisher.getStartIndex() + split + 1), (bibRef.journalOrPublisher.size() - split - 1));
			bibRef.location = Gamta.newAnnotation(bibRef.annotation, LOCATION_ANNOTATION_TYPE, bibRef.journalOrPublisher.getStartIndex(), split);
		}
		else {
			bibRef.publisher = Gamta.newAnnotation(bibRef.annotation, PUBLISHER_ANNOTATION_TYPE, bibRef.journalOrPublisher.getStartIndex(), split);
			bibRef.location = Gamta.newAnnotation(bibRef.annotation, LOCATION_ANNOTATION_TYPE, (bibRef.journalOrPublisher.getStartIndex() + split + 1), (bibRef.journalOrPublisher.size() - split - 1));
		}
		return true;
	}
	
	private void annotateDetails(BibRef bibRef) {
		
		//	truncate and unify page data
		if (bibRef.pagination != null) {
			int start = bibRef.pagination.getStartIndex();
			while ((start < bibRef.pagination.getEndIndex()) && !Gamta.isNumber(bibRef.annotation.valueAt(start)))
				start++;
			if (start != bibRef.pagination.getStartIndex())
				bibRef.pagination = Gamta.newAnnotation(bibRef.annotation, bibRef.pagination.getType(), start, (bibRef.pagination.getEndIndex() - start));
			bibRef.pagination.setAttribute(TYPE_ATTRIBUTE, bibRef.pagination.getType());
			bibRef.pagination.changeTypeTo(PAGINATION_ANNOTATION_TYPE);
		}
		
		//	add annotations
		if (bibRef.authors != null)
			for (int a = 0; a < bibRef.authors.length; a++)
				bibRef.annotation.addAnnotation(bibRef.authors[a]);
		if (bibRef.editors != null)
			for (int e = 0; e < bibRef.editors.length; e++)
				bibRef.annotation.addAnnotation(bibRef.editors[e]);
		if (bibRef.year != null)
			bibRef.annotation.addAnnotation(bibRef.year);
		if (bibRef.title != null)
			bibRef.annotation.addAnnotation(bibRef.title);
		
		//	handle volume reference details in an integrated manner
		if (bibRef.volumeDesignator != null)
			bibRef.annotation.addAnnotation(bibRef.volumeDesignator);
		if (bibRef.issueDesignator != null)
			bibRef.annotation.addAnnotation(bibRef.issueDesignator);
		if (bibRef.numberDesignator != null)
			bibRef.annotation.addAnnotation(bibRef.numberDesignator);
		
		if (bibRef.volumeTitle != null)
			bibRef.annotation.addAnnotation(bibRef.volumeTitle);
		if (bibRef.journalOrPublisher != null)
			bibRef.annotation.addAnnotation(bibRef.journalOrPublisher);
		
		if (bibRef.pagination != null)
			bibRef.annotation.addAnnotation(bibRef.pagination);
		
		//	set type attribute here
		if (bibRef.type != null)
			bibRef.annotation.setAttribute(PUBLICATION_TYPE_ATTRIBUTE, bibRef.type.name);
		
		if (DEBUG) System.out.println("Result for reference " + bibRef.annotation.toXML());
		
		//	annotate DOIs ...
		for (int d = 0; d < bibRef.dois.length; d++) {
			if (DEBUG) System.out.println("DOI: " + bibRef.dois[d].toXML());
			bibRef.annotation.addAnnotation(PUBLICATION_DOI_ANNOTATION_TYPE, bibRef.dois[d].getStartIndex(), bibRef.dois[d].size());
		}
		
		//	 ... and URLs ...
		for (int u = 0; u < bibRef.urls.length; u++) {
			if (DEBUG) System.out.println("URL: " + bibRef.urls[u].toXML());
			bibRef.annotation.addAnnotation(PUBLICATION_URL_ANNOTATION_TYPE, bibRef.urls[u].getStartIndex(), bibRef.urls[u].size());
		}
		
		//	... and book content info
		for (int i = 0; i < bibRef.bookContentInfos.size(); i++) {
			Annotation bci = ((Annotation) bibRef.bookContentInfos.get(i));
			if (DEBUG) System.out.println("Book Content Info: " + bci.toXML());
			bibRef.annotation.addAnnotation(BOOK_CONTENT_INFO_ANNOTATION_TYPE, bci.getStartIndex(), bci.size());
		}
		
		//	filter URLs that are also DOIs
		AnnotationFilter.removeContained(bibRef.annotation, PUBLICATION_DOI_ANNOTATION_TYPE, PUBLICATION_URL_ANNOTATION_TYPE);
		AnnotationFilter.removeContaining(bibRef.annotation, PUBLICATION_URL_ANNOTATION_TYPE, PUBLICATION_DOI_ANNOTATION_TYPE);
		
		//	print data
		if (DEBUG) {
			System.out.println("authorList: " + ((bibRef.authorList == null) ? "" : bibRef.authorList.getValue()));
			if (bibRef.authors != null)
				for (int a = 0; a < bibRef.authors.length; a++)
					System.out.println("  - " + bibRef.authors[a].getValue());
			System.out.println("year: " + ((bibRef.year == null) ? "" : bibRef.year.getValue()));
			System.out.println("title: " + ((bibRef.title == null) ? "" : bibRef.title.getValue()));
			if (bibRef.editors != null) {
				System.out.println("editorList:");
				for (int e = 0; e < bibRef.editors.length; e++)
					System.out.println("  - " + bibRef.editors[e].getValue());
			}
			System.out.println("volume title: " + ((bibRef.volumeTitle == null) ? "" : bibRef.volumeTitle.getValue()));
			System.out.println("journal/publisher: " + ((bibRef.journalOrPublisher == null) ? "" : bibRef.journalOrPublisher.getValue()));
			System.out.println("volume: " + ((bibRef.volumeDesignator == null) ? "" : bibRef.volumeDesignator.getValue()));
			System.out.println("page(s): " + ((bibRef.pagination == null) ? "" : bibRef.pagination.getValue()));
			System.out.println();
		}
	}
	
	private void classify(final BibRef bibRef) {
//		
//		if (DEBUG) System.out.println("Classifying " + bibRef.annotation.toXML());
//		String typeName = this.referenceTypeSystem.classify(new AbstractAttributed() {
//			public Object getAttribute(String name, Object def) {
//				if (TITLE_ANNOTATION_TYPE.equals(name)) {
//					return ((bibRef.title == null) ? def : bibRef.title.getValue());
//				}
//				return super.getAttribute(name, def);
//			}
//			public Object getAttribute(String name) {
//				return this.getAttribute(name, null);
//			}
//			public boolean hasAttribute(String name) {
//				return (this.getAttribute(name) != null);
//			}
//		});
//		if (DEBUG) System.out.println(" ==> classified as " + typeName);
//		bibRef.type = ((BibRefType) this.referenceTypes.get(typeName));
		
		if (DEBUG) System.out.println("Classifying " + bibRef.annotation.toXML());
		String typeName = "";
		
		//	got pagination ==> part of something
		boolean gotPagination = (bibRef.pagination != null);
		if (DEBUG) System.out.println(" - page data " + (gotPagination ? "" : "not ") + "given");
		
		//	got volume, issue, or number designator
		boolean gotPartDesignator = ((bibRef.volumeDesignator != null) || (bibRef.issueDesignator != null) || (bibRef.numberDesignator != null));
		if (DEBUG) System.out.println(" - part designator " + (gotPartDesignator ? "" : "not ") + "given");
		
		//	check book content hints
		boolean gotBookContentInfos = (bibRef.bookContentInfos.size() != 0);
		if (DEBUG) System.out.println(" - book content info " + (gotBookContentInfos ? "" : "not ") + "given");
		
		//	clearly a book
		if (gotBookContentInfos) {
			if (DEBUG) System.out.println(" --> using book content hint");
			typeName = (gotPagination ? BOOK_CHAPTER_REFERENCE_TYPE : BOOK_REFERENCE_TYPE);
		}
		
		//	clearly a journal or part of one
		else if (gotPartDesignator) {
			if (DEBUG) System.out.println(" --> using part designator hint");
			typeName = (gotPagination ? JOURNAL_ARTICEL_REFERENCE_TYPE : JOURNAL_VOLUME_REFERENCE_TYPE);
		}
		
		//	part of book or proceedings
		else if (gotPagination) {
			if (DEBUG) System.out.println(" --> using page data and journal / publisher name" + ((bibRef.journalOrPublisher == null) ? " (missing)" : (": " + TokenSequenceUtils.concatTokens(bibRef.journalOrPublisher, true, true))));
			typeName = (((bibRef.journalOrPublisher != null) && bibRef.journalOrPublisher.firstValue().toLowerCase().startsWith("proc")) ? PROCEEDINGS_PAPER_REFERENCE_TYPE : BOOK_CHAPTER_REFERENCE_TYPE);
		}
		
		//	part of proceedings with missing page data
		else if ((bibRef.journalOrPublisher != null) && bibRef.journalOrPublisher.firstValue().toLowerCase().startsWith("proc")) {
			if (DEBUG) System.out.println(" --> using journal / publisher name: " + TokenSequenceUtils.concatTokens(bibRef.journalOrPublisher, true, true));
			typeName = PROCEEDINGS_PAPER_REFERENCE_TYPE;
		}
		
		//	book or proceedings
		else {
			if (DEBUG) System.out.println(" --> using title" + ((bibRef.title == null) ? " (missing)" : (": " + TokenSequenceUtils.concatTokens(bibRef.title, true, true))));
			typeName = (((bibRef.title != null) && bibRef.title.firstValue().toLowerCase().startsWith("proc")) ? PROCEEDINGS_REFERENCE_TYPE : BOOK_REFERENCE_TYPE); 
		}
		
		//	set type
		if (DEBUG) System.out.println(" ==> classified as " + typeName);
		bibRef.type = ((BibRefType) this.referenceTypes.get(typeName));
	}
	
	void learnDetails(MutableAnnotation bibRef) {
		
		//	learn author names, and also editor names, might be authors somewhere else
		Annotation[] feedbackAuthors = bibRef.getAnnotations(AUTHOR_ANNOTATION_TYPE);
		for (int a = 0; a < feedbackAuthors.length; a++)
			this.knownAuthors.addEntry(feedbackAuthors[a].getValue());
		Annotation[] feedbackEditors = bibRef.getAnnotations(EDITOR_ANNOTATION_TYPE);
		for (int e = 0; e < feedbackEditors.length; e++)
			this.knownAuthors.addEntry(feedbackEditors[e].getValue());
		
		//	TODO distinguish journal names from publishers and publisher locations
		boolean[] isJop = new boolean[bibRef.size()];
		Arrays.fill(isJop, false);
		Annotation[] feedbackJournalsAndPublishers = bibRef.getAnnotations(JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE);
		for (int jp = 0; jp < feedbackJournalsAndPublishers.length; jp++) {
			this.knownJournalsAndPublishers.addEntry(feedbackJournalsAndPublishers[jp].getValue());
			for (int t = feedbackJournalsAndPublishers[jp].getStartIndex(); t < feedbackJournalsAndPublishers[jp].getEndIndex(); t++)
				isJop[t] = true;
		}
		
		//	learn word functions
		for (int t = 0; t < bibRef.size(); t++) {
			String v = bibRef.valueAt(t);
			if (Gamta.isWord(v) && (v.length() > 1))
				this.jopWordStat.count(v, isJop[t], ((t == 0) || !isJop[t-1]), (((t+1) == bibRef.size()) || !isJop[t+1]));
		}
	}
	
	static class BibRefType implements Comparable {
		final String name;
		final String label;
		BibRefType(String name, String label) {
			this.name = name;
			this.label = label;
		}
		BibRefType(String name) {
			this.name = name;
			this.label = "COMPARISON DUMMY";
		}
		public int hashCode() {
			return this.name.hashCode();
		}
		public boolean equals(Object obj) {
			return ((obj instanceof BibRefType) && this.name.equals(((BibRefType) obj).name));
		}
		public int compareTo(Object obj) {
			return this.name.compareTo(((BibRefType) obj).name);
		}
		public String toString() {
			return this.label; // required for Swing version of feedback panel
		}
		public String toDataString() {
			return (this.name + "|" + this.label);
		}
		public static BibRefType parseDataString(String dataString) {
			String[] data = dataString.split("\\|");
			return ((data.length == 2) ? new BibRefType(data[0], data[1]) : null);
		}
	}
	
	//	use array of instances of this class as data containers instead of individual arrays ==> facilitates splitting 1,000 line parsing method
	private class BibRef {
		MutableAnnotation annotation;
		
		Annotation[] authorNames;
		AuthorList[] authorLists;
		Annotation authorList;
		Annotation[] authors;
		
		Annotation[] editors;
		
		Annotation[] years;
		Annotation year;
		
		Annotation[] urls;
		Annotation[] dois;
		
		Annotation[] pageNumbers;
		Annotation[] pageRanges;
		Annotation pagination;
		
		Annotation[] partDesignators;
		HashMap partDesignatorHints = new HashMap();
		Annotation[] volumeDesignators;
		Annotation volumeDesignator;
		Annotation[] issueDesignators;
		Annotation issueDesignator;
		Annotation[] numberDesignators;
		Annotation numberDesignator;
		Annotation[] seriesDesignators;
		Annotation seriesDesignator;
		Annotation[] fascicleDesignators;
		Annotation fascicleDesignator;
		
		Annotation[] wordBlocks;
		boolean[] wordBlockExcluded;
		
		Annotation journalOrPublisher;
		Annotation journal;
		Annotation publisher;
		Annotation location;
		Annotation proceedingsVolumeTitle;
		
		Annotation title;
		Annotation volumeTitle;
		
		BibRef parentRef;
		BibRef volumeRef;
		Annotation volumeReference;
		
		ArrayList bookContentInfos = new ArrayList();
		HashSet titleNumberTokens = new HashSet();
		BibRefType type;
		
		boolean preExistingStructure = false;
		ArrayList structures = new ArrayList();
		Structure structure;
		
		BibRef(MutableAnnotation annot) {
			this.annotation = annot;
			
			int preExistingStructureScore = 0;
			if (this.annotation.getAnnotations(AUTHOR_ANNOTATION_TYPE).length != 0)
				preExistingStructureScore++;
			if (this.annotation.getAnnotations(TITLE_ANNOTATION_TYPE).length != 0)
				preExistingStructureScore++;
			if (this.annotation.getAnnotations(YEAR_ANNOTATION_TYPE).length != 0)
				preExistingStructureScore++;
			this.preExistingStructure = (preExistingStructureScore >= 2);
		}
	}
	
	private class Structure {
		Annotation bibRef;
		String[] details;
		
		String[] types;
		String typeString;
		String[] summary;
		String summaryString;
		String[] punctSummary;
		String punctSummaryString;
		
		String firstDetail;
		StringVector detailTypes = new StringVector();
		int maxVoidBlockLength = 0;
		
		Structure(Annotation bibRef, String[] workingStructure) {
			this.bibRef = bibRef;
			
			this.details = new String[workingStructure.length];
			System.arraycopy(workingStructure, 0, this.details, 0, workingStructure.length);
			
			int voidBlockLength = 0;
			for (int d = 0; d < this.details.length; d++) { 
				if (this.details[d] == null) {
					this.details[d] = "_";
					voidBlockLength++;
				}
				else { 
					this.detailTypes.addElementIgnoreDuplicates(this.details[d]);
					if (this.firstDetail == null)
						this.firstDetail = this.details[d];
					if (voidBlockLength > this.maxVoidBlockLength)
						this.maxVoidBlockLength = voidBlockLength;
					voidBlockLength = 0;
				}
			}
			if (voidBlockLength > this.maxVoidBlockLength)
				this.maxVoidBlockLength = voidBlockLength;
			
			this.types = this.detailTypes.toStringArray();
			this.typeString = this.detailTypes.concatStrings(" ");
			
			StringVector summary = new StringVector();
			String summaryLast = null;
			
			StringVector punctSummary = new StringVector();
			String punctSummaryLast = null;
			
			for (int d = 0; d < this.details.length; d++) {
				if ((d != 0) && YEAR_ANNOTATION_TYPE.equals(this.details[d-1]) && "_".equals(this.details[d]) && this.bibRef.valueAt(d).matches("[a-z]"))
					continue; // skip over single lower case letters following year of publication
				
				String summaryAdd = this.details[d];
				if ((d == 0) || !summaryLast.equals(summaryAdd)) {
					summary.addElement(summaryAdd);
					summaryLast = summaryAdd;
				}
				
				String punctSummaryAdd = (("_".equals(this.details[d]) && Gamta.isPunctuation(this.bibRef.valueAt(d))) ? this.bibRef.valueAt(d) : this.details[d]);
				if ((d == 0) || !punctSummaryLast.equals(punctSummaryAdd)) {
					punctSummary.addElement(punctSummaryAdd);
					punctSummaryLast = punctSummaryAdd;
				}
			}
			
			this.summary = summary.toStringArray();
			this.summaryString = summary.concatStrings(" ");
			
			for (int p = 0; p < punctSummary.size(); p++)
				if ("_".equals(punctSummary.get(p))) {
					for (int l = (p+1); l < punctSummary.size(); l++) {
						if (!Gamta.isPunctuation(punctSummary.get(l)))
							l = punctSummary.size();
						else if ("_".equals(punctSummary.get(l))) {
							while (p < l)
								punctSummary.removeElementAt(l--);
							l = punctSummary.size();
							p--;
						}
					}
				}
			
			this.punctSummary = punctSummary.toStringArray();
			this.punctSummaryString = punctSummary.concatStrings(" ");
		}
	}
	
	private static final String namePartOrder = "npo";
	private static final String firstLastNPO = "FL";
	private static final String lastFirstNPO = "LF";
	
	private static final String firstNameStyle = "fns";
	private static final String fullNameFNS = "N";
	private static final String initialsFNS = "I";
	
	private static final String etAlSpecialType = "etAl";
	static final String repetitionMarkerSpecialType = "alrm";
	private static final String knownAuthorMarker = "kam";
	
	private Annotation[] getAuthorNames(Annotation bibRef) {
		
		//	get author name parts
		ArrayList authorNamePartList = new ArrayList();
		
		//	last names
		Annotation[] lastNames = Gamta.extractAllMatches(bibRef, this.authorLastNameRegEx, true);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - author last names:");
		for (int l = 0; l < lastNames.length; l++) {
			if (!this.hasVowel(lastNames[l]))
				continue;
			authorNamePartList.add(lastNames[l]);
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + lastNames[l]);
		}
		if (authorNamePartList.size() < lastNames.length)
			lastNames = ((Annotation[]) authorNamePartList.toArray(new Annotation[authorNamePartList.size()]));
		authorNamePartList.clear();
		
		//	stop word blocks
		this.authorNameStopWords.sortByLength(true);
		String stopWordRegEx = RegExUtils.produceOrGroup(this.authorNameStopWords.toStringArray(), false);
		Annotation[] stopWordBlocks = Gamta.extractAllMatches(bibRef, ("(" + stopWordRegEx + "(\\s+" + stopWordRegEx + ")*)"), false);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - stop word blocks:");
		for (int s = 0; s < stopWordBlocks.length; s++) {
			if (!this.hasVowel(stopWordBlocks[s]))
				continue;
			authorNamePartList.add(stopWordBlocks[s]);
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + stopWordBlocks[s]);
		}
		if (authorNamePartList.size() < stopWordBlocks.length)
			stopWordBlocks = ((Annotation[]) authorNamePartList.toArray(new Annotation[authorNamePartList.size()]));
		authorNamePartList.clear();
		
		//	first names
		Annotation[] firstNames = Gamta.extractAllMatches(bibRef, this.authorFirstNameRegEx, true);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - first names:");
		for (int f = 0; f < firstNames.length; f++) {
			if (!this.hasVowel(firstNames[f]))
				continue;
			authorNamePartList.add(firstNames[f]);
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + firstNames[f]);
		}
		if (authorNamePartList.size() < firstNames.length)
			firstNames = ((Annotation[]) authorNamePartList.toArray(new Annotation[authorNamePartList.size()]));
		authorNamePartList.clear();
		
		//	blocks of initials (need to allow sub-matches here, as otherwise all-caps last names end up conflated with initials)
		Annotation[] initials = Gamta.extractAllMatches(bibRef, this.authorInitialsRegEx, true);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) {
			System.out.println("  - initial blocks:");
			for (int i = 0; i < initials.length; i++)
				System.out.println("    - " + initials[i]);
		}
		
		//	affixes
		Annotation[] affixes = Gamta.extractAllMatches(bibRef, this.authorNameAffixRegEx, false);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) {
			System.out.println("  - affixes:");
			for (int a = 0; a < affixes.length; a++)
				System.out.println("    - " + affixes[a]);
		}
		
		//	build author names
		ArrayList authorNameList = new ArrayList();
		HashSet authorNameStrings = new HashSet();
		AnnotationIndex authorNameParts = new AnnotationIndex();
		authorNameParts.addAnnotations(lastNames, "lastName");
		authorNameParts.addAnnotations(stopWordBlocks, "stopWords");
		authorNameParts.addAnnotations(AnnotationPatternMatcher.getMatches(bibRef, authorNameParts, "<lastName> <stopWords> <lastName>"), "lastName");
		authorNameParts.addAnnotations(firstNames, "firstName");
		authorNameParts.addAnnotations(initials, "initials");
		authorNameParts.addAnnotations(AnnotationPatternMatcher.getMatches(bibRef, authorNameParts, "<firstName> <initials>"), "firstName");
		authorNameParts.addAnnotations(AnnotationPatternMatcher.getMatches(bibRef, authorNameParts, "<initials> <firstName>"), "firstName");
		authorNameParts.addAnnotations(affixes, "affix");
		
		//	last name first, initials
		this.addAuthorNames(bibRef, authorNameParts, "<stopWords>? <lastName> ','? <initials>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<stopWords>? <lastName> ','? <affix> ','? <initials>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<stopWords>? <lastName> ','? <initials>','? <affix>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ','? <initials>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ','? <initials> ','? <stopWords>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ','? <affix> ','? <initials>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ','? <affix> ','? <initials> ','? <stopWords>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ','? <initials> ','? <stopWords>? ','? <affix>", authorNameList, authorNameStrings, lastFirstNPO, initialsFNS);
		authorNameStrings.clear();
		
		//	last name first, full first name
		this.addAuthorNames(bibRef, authorNameParts, "<stopWords>? <lastName> ',' <firstName>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<stopWords>? <lastName> ','? <affix> ',' <firstName>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<stopWords>? <lastName> ',' <firstName>','? <affix>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ',' <firstName>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ',' <firstName> ','? <stopWords>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ','? <affix> ',' <firstName>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ','? <affix> ',' <firstName> ','? <stopWords>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<lastName> ',' <firstName> ','? <stopWords>? ','? <affix>", authorNameList, authorNameStrings, lastFirstNPO, fullNameFNS);
		authorNameStrings.clear();
		
		//	last name last, initials
		this.addAuthorNames(bibRef, authorNameParts, "<initials> <stopWords>? <lastName>", authorNameList, authorNameStrings, firstLastNPO, initialsFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<initials> <stopWords>? <lastName> ','? <affix>", authorNameList, authorNameStrings, firstLastNPO, initialsFNS);
		authorNameStrings.clear();
		
		//	last name last, full first name
		this.addAuthorNames(bibRef, authorNameParts, "<firstName> <stopWords>? <lastName>", authorNameList, authorNameStrings, firstLastNPO, fullNameFNS);
		this.addAuthorNames(bibRef, authorNameParts, "<firstName> <stopWords>? <lastName> ','? <affix>", authorNameList, authorNameStrings, firstLastNPO, fullNameFNS);
		authorNameStrings.clear();
		
		//	extract known author names
		Annotation[] knownAuthorNames = this.knownAuthors.extractAllContained(bibRef, true, this.authorNameStopWords);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - known author names");
		for (int ka = 0; ka < knownAuthorNames.length; ka++) {
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + knownAuthorNames[ka]);
			
			//	add dictionary recognition marker to known pattern matches instead of adding names redundantly
			boolean unseenAuthorName = true;
			for (int a = 0; a < authorNameList.size(); a++) {
				Annotation authorName = ((Annotation) authorNameList.get(a));
				if (AnnotationUtils.equals(knownAuthorNames[ka], authorName, false)) {
					authorName.setAttribute(knownAuthorMarker, knownAuthorMarker);
					unseenAuthorName = false;
				}
			}
			if (DEBUG_AUTHOR_NAME_EXTRACTION && !unseenAuthorName)
				System.out.println("     --> extracted by patterns");
			
			//	retain matches contained in others only if the containing one includes an author list separator immediately before or after contained one
			boolean containedAuthorName = false;
			for (int a = 0; a < authorNameList.size(); a++) {
				Annotation authorName = ((Annotation) authorNameList.get(a));
				if (!AnnotationUtils.contains(authorName, knownAuthorNames[ka]))
					continue;
				if ((authorName.getEndIndex() > knownAuthorNames[ka].getEndIndex()) && !this.authorListSeparators.containsIgnoreCase(bibRef.valueAt(knownAuthorNames[ka].getEndIndex()))) {
					containedAuthorName = true;
					break;
				}
				if ((authorName.getStartIndex() < knownAuthorNames[ka].getStartIndex()) && !this.authorListSeparators.containsIgnoreCase(bibRef.valueAt(knownAuthorNames[ka].getStartIndex()-1))) {
					containedAuthorName = true;
					break;
				}
			}
			if (DEBUG_AUTHOR_NAME_EXTRACTION && containedAuthorName)
				System.out.println("     --> sub match");
			
			//	this one is actually new
			if (unseenAuthorName && !containedAuthorName) {
				if (DEBUG_AUTHOR_NAME_EXTRACTION)
					System.out.println("     --> found author unmatched by patterns");
				knownAuthorNames[ka].setAttribute(namePartOrder, firstLastNPO);
//				knownAuthorNames[ka].setAttribute(firstNameStyle, mixedFNS);
				knownAuthorNames[ka].setAttribute(firstNameStyle, fullNameFNS);
				knownAuthorNames[ka].setAttribute(knownAuthorMarker, knownAuthorMarker);
				authorNameList.add(knownAuthorNames[ka]);
			}
		}
		
		//	mark author names contained in dictionary, and sort out ones with invalid starts
		for (int a = 0; a < authorNameList.size(); a++) {
			Annotation authorName = ((Annotation) authorNameList.get(a));
			if (this.knownNonAuthorNameStarts.contains(authorName.firstValue()))
				authorNameList.remove(a--);
			else if (!authorName.hasAttribute(knownAuthorMarker) && this.knownAuthors.lookup(authorName.getValue()))
				authorName.setAttribute(knownAuthorMarker, knownAuthorMarker);
		}
		
		//	set type for all author names
		for (int a = 0; a < authorNameList.size(); a++)
			((Annotation) authorNameList.get(a)).changeTypeTo(AUTHOR_ANNOTATION_TYPE);
		
		
		//	add "et al." to author names
		Annotation[] etAl = Gamta.extractAllMatches(bibRef, "et\\sal\\.?", false);
		for (int a = 0; a < etAl.length; a++) {
			etAl[a].changeTypeTo(etAlSpecialType);
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + etAl[a]);
			
			Annotation etAlLnCoFn = Gamta.newAnnotation(bibRef, etAl[a]);
			etAlLnCoFn.setAttribute(namePartOrder, lastFirstNPO);
			etAlLnCoFn.setAttribute(firstNameStyle, fullNameFNS);
			authorNameList.add(etAlLnCoFn);
			Annotation etAlLnCoI = Gamta.newAnnotation(bibRef, etAl[a]);
			etAlLnCoI.setAttribute(namePartOrder, lastFirstNPO);
			etAlLnCoI.setAttribute(firstNameStyle, fullNameFNS);
			authorNameList.add(etAlLnCoI);
			Annotation etAlLnI = Gamta.newAnnotation(bibRef, etAl[a]);
			etAlLnI.setAttribute(namePartOrder, lastFirstNPO);
			etAlLnI.setAttribute(firstNameStyle, initialsFNS);
			authorNameList.add(etAlLnI);
			
			//	truncate dot from "et al." for <firstName> <lastName> part order ==> prevents "stealing" data element separator
			if (".".equals(etAl[a].lastValue()))
				etAl[a] = Gamta.newAnnotation(bibRef, etAl[a].getType(), etAl[a].getStartIndex(), (etAl[a].size()-1));
			
			Annotation etAlFnLn = Gamta.newAnnotation(bibRef, etAl[a]);
			etAlFnLn.setAttribute(namePartOrder, firstLastNPO);
			etAlFnLn.setAttribute(firstNameStyle, fullNameFNS);
			authorNameList.add(etAlFnLn);
			Annotation etAlILn = Gamta.newAnnotation(bibRef, etAl[a]);
			etAlILn.setAttribute(namePartOrder, firstLastNPO);
			etAlILn.setAttribute(firstNameStyle, initialsFNS);
			authorNameList.add(etAlILn);
		}
		
		//	mark author list repetition markers
		Annotation[] authorRepetitionMarkers = Gamta.extractAllMatches(bibRef, this.authorRepetitionMarkerRegEx, false);
		for (int a = 0; a < authorRepetitionMarkers.length; a++) {
			if ((authorRepetitionMarkers[a].length() < 2 ) && (authorRepetitionMarkers[a].getStartIndex() > 2))
				continue;
			authorRepetitionMarkers[a].changeTypeTo(repetitionMarkerSpecialType);
			
			Annotation armLnCoFn = Gamta.newAnnotation(bibRef, authorRepetitionMarkers[a]);
			armLnCoFn.setAttribute(namePartOrder, lastFirstNPO);
			armLnCoFn.setAttribute(firstNameStyle, fullNameFNS);
			authorNameList.add(armLnCoFn);
			Annotation armLnCoI = Gamta.newAnnotation(bibRef, authorRepetitionMarkers[a]);
			armLnCoI.setAttribute(namePartOrder, lastFirstNPO);
			armLnCoI.setAttribute(firstNameStyle, initialsFNS);
			authorNameList.add(armLnCoI);
			Annotation armLnI = Gamta.newAnnotation(bibRef, authorRepetitionMarkers[a]);
			armLnI.setAttribute(namePartOrder, lastFirstNPO);
			armLnI.setAttribute(firstNameStyle, initialsFNS);
			authorNameList.add(armLnI);
			Annotation armFnLn = Gamta.newAnnotation(bibRef, authorRepetitionMarkers[a]);
			armFnLn.setAttribute(namePartOrder, firstLastNPO);
			armFnLn.setAttribute(firstNameStyle, fullNameFNS);
			authorNameList.add(armFnLn);
			Annotation armILn = Gamta.newAnnotation(bibRef, authorRepetitionMarkers[a]);
			armILn.setAttribute(namePartOrder, firstLastNPO);
			armILn.setAttribute(firstNameStyle, initialsFNS);
			authorNameList.add(armILn);
			
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + authorRepetitionMarkers[a]);
		}
		
		//	finally ...
		Annotation[] authorNames = ((Annotation[]) authorNameList.toArray(new Annotation[authorNameList.size()]));
		Arrays.sort(authorNames);
		return authorNames;
	}
	
	private void addAuthorNames(Annotation bibRef, AnnotationIndex authorNameParts, String authorNamePattern, ArrayList authorNameList, HashSet authorNameStrings, String namePartOrderKey, String firstNameStyleKey) {
		Annotation[] authorNames = AnnotationPatternMatcher.getMatches(bibRef, authorNameParts, authorNamePattern);
		if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("  - " + authorNames.length + " authors " + authorNamePattern + ":");
		for (int a = 0; a < authorNames.length; a++) {
			authorNames[a].setAttribute(namePartOrder, namePartOrderKey);
			authorNames[a].setAttribute(firstNameStyle, firstNameStyleKey);
			if (authorNameStrings.add(authorNames[a].getStartIndex() + "-" + authorNames[a].getValue()))
				authorNameList.add(authorNames[a]);
			if (DEBUG_AUTHOR_NAME_EXTRACTION) System.out.println("    - " + authorNames[a]);
		}
	}
	
	private void getAuthorLists(BibRef bibRef) {
		
		//	this one has been parsed before, use what's there
		if (bibRef.preExistingStructure) {
			
			//	build author list from existing authors
			if (bibRef.authorNames.length != 0)
				bibRef.authorList = Gamta.newAnnotation(bibRef.annotation, AUTHOR_LIST_ANNOTATION_TYPE, bibRef.authorNames[0].getStartIndex(), (bibRef.authorNames[bibRef.authorNames.length-1].getEndIndex() - bibRef.authorNames[0].getStartIndex()));
			
			//	we're done here
			return;
		}
		
		//	this one's new
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Building author lists in " + bibRef.annotation.toXML());
		
		//	make noble titles bridgeable
		Annotation[] nobleTitles = Gamta.extractAllMatches(bibRef.annotation, this.nobleTitleNameRegEx, false);
		boolean[] isNobleTitleToken = new boolean[bibRef.annotation.size()];
		Arrays.fill(isNobleTitleToken, false);
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  - possible noble titles");
		for (int n = 0; n < nobleTitles.length; n++) {
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("    - " + nobleTitles[n]);
			if (this.nobleTitleStarts.contains(nobleTitles[n].firstValue())) {
				for (int t = nobleTitles[n].getStartIndex(); t < nobleTitles[n].getEndIndex(); t++)
					isNobleTitleToken[t] = true;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("    --> marked");
			}
			else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("    --> ignored for strange start");
		}
		
		//	make stray name affixes bridgeable
		Annotation[] nameAffixes = Gamta.extractAllMatches(bibRef.annotation, this.authorNameAffixRegEx, false);
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  - possible affixes");
		for (int n = 0; n < nameAffixes.length; n++) {
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("    - " + nameAffixes[n]);
			for (int t = nameAffixes[n].getStartIndex(); t < nameAffixes[n].getEndIndex(); t++)
				isNobleTitleToken[t] = true;
		}
		
		//	generate author lists
		ArrayList authorLists = new ArrayList();
		this.buildAuthorLists(bibRef, isNobleTitleToken, new LinkedList(), -1, null, null, new HashSet(), new HashSet(), authorLists);
		
		//	filter out author lists consisting single author names like of "Washington, DC", etc.
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Sorting out known city names:");
		for (int l = 0; l < authorLists.size(); l++) {
			AuthorList al = ((AuthorList) authorLists.get(l));
			if (al.authorNames.size() > 1)
				continue;
			Annotation an = ((Annotation) al.authorNames.get(0));
			String ans = an.getValue();
			ans = ans.replaceAll("[^A-Za-z]", "");
			if (this.knownNonAuthorNames.containsIgnoreCase(ans)) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println(" - removig for known negative: " + al.annotation);
				authorLists.remove(l--);
			}
		}
		
		//	sort out author lists that are sub sets of others, and mark sub lists
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Sorting out sub lists:");
		for (int l = 0; l < authorLists.size(); l++) {
			AuthorList al = ((AuthorList) authorLists.get(l));
			boolean contained = false;
			for (int c = 0; c < authorLists.size(); c++) {
				if (c == l)
					continue;
				AuthorList cal = ((AuthorList) authorLists.get(c));
				if ((al.firstNameStyles.size() != cal.firstNameStyles.size()) || !cal.firstNameStyles.containsAll(al.firstNameStyles))
					continue;
				if (!AnnotationUtils.liesIn(al.annotation, cal.annotation))
					continue;
				if (!cal.namePartOrders.containsAll(al.namePartOrders))
					continue;
				if (al.namePartOrders.size() != cal.namePartOrders.size()) {
					al.isSubList = true;
					continue;
				}
				if (!al.bridged.containsAll(cal.bridged))
					continue;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) {
					System.out.println(" - removing " + al.annotation);
					System.out.println("    - names: " + al.authorNames);
					System.out.println("    - bridged: " + al.bridged);
					System.out.println("    - name part orders: " + al.namePartOrders);
					System.out.println("    - first name sytles: " + al.firstNameStyles);
					System.out.println("    - contained in " + cal.annotation);
					System.out.println("      - names: " + cal.authorNames);
					System.out.println("      - bridged: " + cal.bridged);
					System.out.println("      - name part orders: " + cal.namePartOrders);
					System.out.println("      - first name sytles: " + cal.firstNameStyles);
				}
				contained = true;
				break;
			}
			if (contained)
				authorLists.remove(l--);
		}
		
		//	get editor list labels
		Annotation[] editorListLabels = Gamta.extractAllMatches(bibRef.annotation, this.editorListTagRegEx);
		HashMap editorListLabelsByIndex = new HashMap();
		for (int e = 0; e < editorListLabels.length; e++) {
			editorListLabelsByIndex.put(new Integer(editorListLabels[e].getStartIndex()), editorListLabels[e]);
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Editor list label: " + editorListLabels[e]);
		}
		
		//	store author lists
		bibRef.authorLists = new AuthorList[authorLists.size()];
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Author lists:");
		for (int l = 0; l < authorLists.size(); l++) {
			AuthorList authorList = ((AuthorList) authorLists.get(l));
			bibRef.authorLists[l] = authorList;
			
			//	add editor list label
			Annotation editorListLabel = ((Annotation) editorListLabelsByIndex.get(new Integer(authorList.annotation.getEndIndex())));
			if (editorListLabel == null)
				editorListLabel = ((Annotation) editorListLabelsByIndex.get(new Integer(authorList.annotation.getEndIndex() + 1)));
			if ((editorListLabel == null) && VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRef.annotation.getType())) {
				int lookahead = 1;
				while ((editorListLabel == null) && (lookahead < 7))
					editorListLabel = ((Annotation) editorListLabelsByIndex.get(new Integer(authorList.annotation.getEndIndex() + lookahead++)));
			}
			if (editorListLabel != null) {
				Annotation eAuthorListAnnotation = Gamta.newAnnotation(bibRef.annotation, authorList.annotation.getType(), authorList.annotation.getStartIndex(), (editorListLabel.getEndIndex() - authorList.annotation.getStartIndex()));
				eAuthorListAnnotation.copyAttributes(authorList.annotation);
				authorList.annotation = eAuthorListAnnotation;
				authorList.hasEditorListLabel = true;
			}
			
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) {
				System.out.println("  - " + authorList.annotation);
				System.out.println("    - names: " + authorList.authorNames);
				System.out.println("    - bridged: " + authorList.bridged);
				System.out.println("    - name part orders: " + authorList.namePartOrders);
				System.out.println("    - first name sytles: " + authorList.firstNameStyles);
			}
		}
		Arrays.sort(bibRef.authorLists, new Comparator() {
			public int compare(Object o1, Object o2) {
				return AnnotationUtils.compare(((AuthorList) o1).annotation, ((AuthorList) o2).annotation);
			}
		});
	}
	
	private static class AuthorList {
		boolean hasEditorListLabel = false;
		boolean isSubList = false;
		Annotation annotation;
		ArrayList authorNames = new ArrayList();
		LinkedHashSet namePartOrders = new LinkedHashSet();
		LinkedHashSet firstNameStyles = new LinkedHashSet();
		HashSet bridged = new HashSet();
		AuthorList(Annotation bibRef, LinkedList authorNames, boolean[] isNobleTitleToken) {
			int startIndex = -1;
			int endIndex = -1;
			for (Iterator ait = authorNames.iterator(); ait.hasNext();) {
				Annotation authorName = ((Annotation) ait.next());
				this.authorNames.add(authorName);
				this.namePartOrders.add(authorName.getAttribute(namePartOrder));
				this.firstNameStyles.add(authorName.getAttribute(firstNameStyle));
				if (startIndex == -1)
					startIndex = authorName.getStartIndex();
				else for (int b = endIndex; b < authorName.getStartIndex(); b++) {
					if (!isNobleTitleToken[b])
						this.bridged.add(bibRef.valueAt(b));
				}
				endIndex = authorName.getEndIndex();
			}
			this.annotation = Gamta.newAnnotation(bibRef, AUTHOR_LIST_ANNOTATION_TYPE, startIndex, (endIndex - startIndex));
		}
	}
	
	private boolean buildAuthorLists(BibRef bibRef, boolean[] isNobleTitleToken, LinkedList currentAuthorList, int currentAuthorListEnd, String currentNamePartOrder, String currentFirstNameStyle, HashSet attachedAuthorNameIDs, HashSet invokerSubAttachedAuthorNameIDs, ArrayList authorLists) {
		
		//	TODO use annotation patterns here
		
		//	TODO tag all them list separators
		
		//	TODO use any possible author list (make sure to observe '...' and '. . . ' emphases)
		
		boolean stored = false;
		boolean storedPrefix = false;
		HashSet ownSubAttachedAuthorNameIDs = new HashSet();
		for (int a = 0; a < bibRef.authorNames.length; a++) {
			
			//	exploit that author lists do need separator punctuation, regardless of name part order
			if (bibRef.authorNames[a].getStartIndex() <= currentAuthorListEnd)
				continue;
			
			//	this one has been attached by a recursive call already
			if (ownSubAttachedAuthorNameIDs.contains(bibRef.authorNames[a].getAnnotationID()))
				continue;
			
			//	mismatch in first name style, we cannot use this one
			if ((currentFirstNameStyle != null) && !currentFirstNameStyle.equals(bibRef.authorNames[a].getAttribute(firstNameStyle)))
				continue;
			
			//	get current style
			String npOrder = ((currentNamePartOrder == null) ? ((String) bibRef.authorNames[a].getAttribute(namePartOrder)) : currentNamePartOrder);
			String fnStyle = ((currentFirstNameStyle == null) ? ((String) bibRef.authorNames[a].getAttribute(firstNameStyle)) : currentFirstNameStyle);
			
			//	first author in list, start with it
			if (currentAuthorList.isEmpty()) {
				if (etAlSpecialType.equals(bibRef.authorNames[a].getType())) {
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Cannot start author list with " + bibRef.authorNames[a].getValue());
					continue;
				}
				else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Starting author list with " + bibRef.authorNames[a].getValue());
				
				//	this one was part of another list before
				if (attachedAuthorNameIDs.contains(bibRef.authorNames[a].getAnnotationID())) {
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println(" ==> no use, would be suffix");
					continue;
				}
				
				//	we are all last name first, cannot start with anything else
				String sNpOrder = ((String) bibRef.authorNames[a].getAttribute(namePartOrder));
				if (lastFirstNPO.equals(currentNamePartOrder) && !currentNamePartOrder.equals(sNpOrder)) {
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println(" ==> cannot start with " + sNpOrder + " in " + currentNamePartOrder + " document");
					continue;
				}
				
				//	start author list
				currentAuthorList.addLast(bibRef.authorNames[a]);
				boolean subStored = this.buildAuthorLists(bibRef, isNobleTitleToken, currentAuthorList, bibRef.authorNames[a].getEndIndex(), npOrder, fnStyle, attachedAuthorNameIDs, ownSubAttachedAuthorNameIDs, authorLists);
				if (repetitionMarkerSpecialType.equals(bibRef.authorNames[a].getType()))
					subStored = false;
				
				//	no further extensions found, store author list as is now
				if (!subStored)
					authorLists.add(new AuthorList(bibRef.annotation, currentAuthorList, isNobleTitleToken));
				
				//	clean up
				currentAuthorList.removeLast();
				invokerSubAttachedAuthorNameIDs.add(bibRef.authorNames[a].getAnnotationID());
				continue;
			}
			
			if (repetitionMarkerSpecialType.equals(bibRef.authorNames[a].getType())) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - cannot attach repetition marker");
				continue;
			}
			
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println(" - trying to attach " + bibRef.authorNames[a].getValue() + " (" + a + " of " + bibRef.authorNames.length + ") to list of " + currentAuthorList.size());
			
			if ((currentAuthorListEnd + 10) < bibRef.authorNames[a].getStartIndex()) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - too far out");
				break;
			}
			
			//	some pre-checks for years and volume reference starts (prevents bridging to known editor name)
			String bridgeKiller = null;
			for (int b = currentAuthorListEnd; (b < bibRef.authorNames[a].getStartIndex()); b++) {
				String toBridge = bibRef.annotation.valueAt(b);
				
				//	NEVER bridge 'in:', 'In:', ', in', '. In'
				if ("in en".indexOf(toBridge.toLowerCase()) != -1) {
					if (((b+1) < bibRef.authorNames[a].getStartIndex()) && (":".equals(bibRef.annotation.valueAt(b+1)))) {
						bridgeKiller = (toBridge + ":");
						break;
					}
					else if ((b > currentAuthorListEnd) && (",.".indexOf(bibRef.annotation.valueAt(b-1)) != -1)) {
						bridgeKiller = (bibRef.annotation.valueAt(b-1) + " " + toBridge);
						break;
					}
				}
				
				//	NEVER bridge a four-digit number
				else if (toBridge.matches(this.yearRegEx)) {
					bridgeKiller = toBridge;
					break;
				}
			}
			if (bridgeKiller != null) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - cannot bridge over " + bridgeKiller);
				break;
			}
			
			//	check for matching first name style (mixed style allows all)
			boolean canAttachAuthorName = fnStyle.equals(bibRef.authorNames[a].getAttribute(firstNameStyle));
			boolean namePartOrderChanged = false;
			
			//	we don't know this one, but it looks promising so far ...
			if (canAttachAuthorName) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - author name style OK");
				
				//	check for name part order (allow for one switch from last-fist to first-last after one author (first author may be different from rest), but not back)
				if (lastFirstNPO.equals(npOrder) && (currentAuthorList.size() == 1)) {
					namePartOrderChanged = !npOrder.equals(bibRef.authorNames[a].getAttribute(namePartOrder));
					npOrder = ((String) bibRef.authorNames[a].getAttribute(namePartOrder));
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - author name part order " + (namePartOrderChanged ? "switch" : "OK"));
				}
				else if (!npOrder.equals(bibRef.authorNames[a].getAttribute(namePartOrder))) {
					canAttachAuthorName = false;
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - author name part order broken");
				}
				else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - author name part order OK");
				
				if (!canAttachAuthorName)
					continue;
				
				//	we know this one, include it
				if (bibRef.authorNames[a].hasAttribute(knownAuthorMarker)) {
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - known author name");
				}
				
				//	check for interrupting tokens
				else for (int b = currentAuthorListEnd; canAttachAuthorName && (b < bibRef.authorNames[a].getStartIndex()); b++) {
					String toBridge = bibRef.annotation.valueAt(b);
					if (!this.authorListSeparators.contains(toBridge) && !isNobleTitleToken[b])
						canAttachAuthorName = false;
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - bridging " + toBridge + " ==> " + (canAttachAuthorName ? "OK" : "broken"));
				}
			}
			
			//	we cannot continue with this one
			else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   - author name style broken");
			
			//	we are going to switch name part order, store current list in case of errors
			if (namePartOrderChanged && !storedPrefix) {
				authorLists.add(new AuthorList(bibRef.annotation, currentAuthorList, isNobleTitleToken));
				stored = true;
				storedPrefix = true;
			}
			
			//	author list continues (bridgeable middle part, or known author name to continue with after at most 10 tokens)
			if (canAttachAuthorName) {
				currentAuthorList.addLast(bibRef.authorNames[a]);
				attachedAuthorNameIDs.add(bibRef.authorNames[a].getAnnotationID());
				boolean subStored;
				
				//	'et al.', do not attempt further extensions
				if (etAlSpecialType.equals(bibRef.authorNames[a].getType()))
					subStored = false;
				
				//	try to continue with further extensions
				else subStored = this.buildAuthorLists(bibRef, isNobleTitleToken, currentAuthorList, bibRef.authorNames[a].getEndIndex(), npOrder, fnStyle, attachedAuthorNameIDs, ownSubAttachedAuthorNameIDs, authorLists);
				
				//	no further extensions found, store author list as is now
				if (!subStored)
					authorLists.add(new AuthorList(bibRef.annotation, currentAuthorList, isNobleTitleToken));
				
				currentAuthorList.removeLast();
				invokerSubAttachedAuthorNameIDs.add(bibRef.authorNames[a].getAnnotationID());
				stored = true;
			}
		}
		
		//	tell invoker also which names were attached transitively
		invokerSubAttachedAuthorNameIDs.addAll(ownSubAttachedAuthorNameIDs);
		
		//	did we do something?
		return stored;
	}
	
	static class AuthorListStyle implements Comparable {
		final String key;
		LinkedHashSet namePartOrders = new LinkedHashSet();
		HashSet firstNameStyles = new HashSet();
		HashSet refIDs = new HashSet();
		int instanceCount = 0;
		int nameCount = 0;
		int tokenCount = 0;
		CountingStringSet bridged = new CountingStringSet();
		CountingStringSet startDistances = new CountingStringSet();
		CountingStringSet endDistances = new CountingStringSet();
		float alignmentScore = 0;
		boolean isLeading = true;
		AuthorListStyle(AuthorList al) {
			this.key = getKey(al);
			this.namePartOrders.addAll(al.namePartOrders);
			this.firstNameStyles.addAll(al.firstNameStyles);
		}
		boolean isCompatible(AuthorList al) {
			return (this.namePartOrders.containsAll(al.namePartOrders) && this.firstNameStyles.containsAll(al.firstNameStyles));
		}
		public int compareTo(Object obj) {
			return this.key.compareTo(((AuthorListStyle) obj).key);
		}
		static String getKey(AuthorList al) {
			return (al.namePartOrders + "-" + al.firstNameStyles);
		}
	}
	
	private static class CountingStringSet {
		private TreeMap content = new TreeMap();
		private int size = 0;
		CountingStringSet() {}
		StringIterator getIterator() {
			final Iterator it = this.content.keySet().iterator();
			return new StringIterator() {
				public boolean hasNext() {
					return it.hasNext();
				}
				public Object next() {
					return it.next();
				}
				public void remove() {}
				public boolean hasMoreStrings() {
					return it.hasNext();
				}
				public String nextString() {
					return ((String) it.next());
				}
			};
		}
		boolean addAll(Collection c) {
			boolean added = false;
			for (Iterator it = c.iterator(); it.hasNext();) {
				Object obj = it.next();
				if (this.add(obj.toString()))
					added = true;
			}
			return added;
		}
		int getCount(String string) {
			Int i = ((Int) this.content.get(string));
			return ((i == null) ? 0 : i.intValue());
		}
//		int getSize() {
//			return this.size;
//		}
		int getElementCount() {
			return this.content.size();
		}
		boolean add(String string) {
			Int i = ((Int) this.content.get(string));
			this.size++;
			if (i == null) {
				this.content.put(string, new Int(1));
				return true;
			}
			else {
				i.increment();
				return false;
			}
		}
//		boolean remove(String string) {
//			Int i = ((Int) this.content.get(string));
//			if (i == null)
//				return false;
//			this.size--;
//			if (i.intValue() > 1) {
//				i.decrement();
//				return false;
//			}
//			else {
//				this.content.remove(string);
//				return true;
//			}
//		}
		private class Int {
			private int value;
			Int(int val) {
				this.value = val;
			}
			int intValue() {
				return this.value;
			}
			void increment() {
				this.value ++;
			}
//			void increment(int i) {
//				this.value += i;
//			}
//			void decrement() {
//				this.value --;
//			}
//			void decrement(int d) {
//				this.value -= d;
//			}
		}
	}
	
	private AuthorListStyle getAuthorListStyle(BibRef[] bibRefs) {
		
		//	cluster author lists by size and style
		TreeMap authorListStyles = new TreeMap();
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].preExistingStructure)
				continue;
			for (int l = 0; l < bibRefs[r].authorLists.length; l++) {
				String alsKey = AuthorListStyle.getKey(bibRefs[r].authorLists[l]);
				AuthorListStyle als = ((AuthorListStyle) authorListStyles.get(alsKey));
				if (als == null) {
					als = new AuthorListStyle(bibRefs[r].authorLists[l]);
					authorListStyles.put(als.key, als);
				}
				if (als.refIDs.add(bibRefs[r].annotation.getAnnotationID()) || (bibRefs.length >= 3)) {
					als.instanceCount++;
					als.nameCount += bibRefs[r].authorLists[l].authorNames.size();
					als.tokenCount += bibRefs[r].authorLists[l].annotation.size();
					als.startDistances.add("" + bibRefs[r].authorLists[l].annotation.getStartIndex());
					als.endDistances.add("" + (bibRefs[r].annotation.size() - bibRefs[r].authorLists[l].annotation.getStartIndex()));
					als.bridged.addAll(bibRefs[r].authorLists[l].bridged);
				}
				
				//	support only if no LF-FL candidate available for this reference!!
				if (bibRefs[r].authorLists[l].isSubList)
					continue;
				
				//	single name list in last-first order, have to support name switching style
				if ((bibRefs[r].authorLists[l].authorNames.size() == 1) && (bibRefs[r].authorLists[l].namePartOrders.contains(lastFirstNPO))) {
					bibRefs[r].authorLists[l].namePartOrders.add(firstLastNPO);
					alsKey = AuthorListStyle.getKey(bibRefs[r].authorLists[l]);
					als = ((AuthorListStyle) authorListStyles.get(alsKey));
					if (als == null) {
						als = new AuthorListStyle(bibRefs[r].authorLists[l]);
						authorListStyles.put(als.key, als);
					}
					if (als.refIDs.add(bibRefs[r].annotation.getAnnotationID()) || (bibRefs.length >= 3)) {
						als.instanceCount++;
						als.nameCount += bibRefs[r].authorLists[l].authorNames.size();
						als.tokenCount += bibRefs[r].authorLists[l].annotation.size();
						als.startDistances.add("" + bibRefs[r].authorLists[l].annotation.getStartIndex());
						als.endDistances.add("" + (bibRefs[r].annotation.size() - bibRefs[r].authorLists[l].annotation.getEndIndex()));
						als.bridged.addAll(bibRefs[r].authorLists[l].bridged);
					}
					
					bibRefs[r].authorLists[l].namePartOrders.remove(firstLastNPO);
				}
			}
		}
		
		//	sort out author lists based on alignment vote
		if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("Author List Styles from " + bibRefs.length + " references:");
		AuthorListStyle authorListStyle = null;
		for (Iterator alsit = authorListStyles.keySet().iterator(); alsit.hasNext();) {
			String alsKey = ((String) alsit.next());
			AuthorListStyle als = ((AuthorListStyle) authorListStyles.get(alsKey));
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) {
				System.out.println(" - " + als.key + " (" + als.instanceCount + " instances in " + als.refIDs.size() + " refs, " + als.nameCount + " names, " + als.tokenCount + " tokens):");
				System.out.print("   - bridged: ");
				for (StringIterator bit = als.bridged.getIterator(); bit.hasMoreStrings();) {
					String b = bit.nextString();
					System.out.print(b + " (" + als.bridged.getCount(b) + ")" + (bit.hasMoreStrings() ? ", " : ""));
				}
				System.out.println();
			}
			
			//	more names than styles, void support vote (can happen with few references)
			if (als.nameCount < als.namePartOrders.size()) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> void support vote");
				continue;
			}
			
			//	too few references to count on redundancy, decide by distinctiveness of structure
			if (bibRefs.length < 3) {
				
				//	score by starting position (far from end)
				int startDistanceSquareSum = 0;
				int endDistanceSquareSum = 0;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print("   - start distances: ");
				for (StringIterator sit = als.startDistances.getIterator(); sit.hasMoreStrings();) {
					String s = sit.nextString();
					int sc = Integer.parseInt(s);
					startDistanceSquareSum -= sc;
					endDistanceSquareSum += sc;
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print(s + " (" + als.startDistances.getCount(s) + ")" + (sit.hasMoreStrings() ? ", " : ""));
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print("   - end distances: ");
				for (StringIterator sit = als.endDistances.getIterator(); sit.hasMoreStrings();) {
					String e = sit.nextString();
					int ec = Integer.parseInt(e);
					startDistanceSquareSum += ec;
					endDistanceSquareSum -= ec;
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print(e + " (" + als.endDistances.getCount(e) + ")" + (sit.hasMoreStrings() ? ", " : ""));
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println();
				
				float startAlignmentScore = (((float) startDistanceSquareSum) / als.startDistances.getElementCount());
				float endAlignmentScore = (((float) endDistanceSquareSum) / als.endDistances.getElementCount());
				
				//	these things only make sense with more than one reference, as an author omission is impossible to detect in a single reference if some possible name is found
				if (bibRefs.length > 1) {
					if (als.firstNameStyles.contains(fullNameFNS)) {
						startAlignmentScore /= 2;
						endAlignmentScore /= 2;
					}
					if (!als.namePartOrders.contains(lastFirstNPO)) {
						startAlignmentScore /= 2;
						endAlignmentScore /= 2;
					}
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) {
					System.out.println("   --> score: " + startAlignmentScore);
					System.out.println("   --> score: " + endAlignmentScore);
				}
				
				als.alignmentScore = Math.max(startAlignmentScore, endAlignmentScore);
				als.isLeading = (endAlignmentScore < startAlignmentScore);
			}
			
			//	we have enough references, use vote
			else {
				
				//	score by number of times starting at same position
				int startDistanceCountSquareSum = 0;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print("   - start distances: ");
				for (StringIterator sit = als.startDistances.getIterator(); sit.hasMoreStrings();) {
					String s = sit.nextString();
					int sc = als.startDistances.getCount(s);
					startDistanceCountSquareSum += (sc * sc);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.print(s + " (" + als.startDistances.getCount(s) + ")" + (sit.hasMoreStrings() ? ", " : ""));
				}
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println();
				
				float startAlignmentScore = (((float) startDistanceCountSquareSum) / als.startDistances.getElementCount());
				if (als.firstNameStyles.contains(fullNameFNS))
					startAlignmentScore /= 2;
				if (!als.namePartOrders.contains(lastFirstNPO))
					startAlignmentScore /= 2;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> score: " + startAlignmentScore);
				
				if ((als.instanceCount * 2) < bibRefs.length) {
					startAlignmentScore = ((startAlignmentScore * als.instanceCount) / bibRefs.length);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> few instance penalty, score set to: " + startAlignmentScore);
				}
				else if ((bibRefs.length * 2) < als.instanceCount) {
					startAlignmentScore = ((startAlignmentScore * bibRefs.length) / als.instanceCount);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> many instance penalty, score set to: " + startAlignmentScore);
				}
				
				int endDistanceCountSquareSum = 0;
				System.out.print("   - end distances: ");
				for (StringIterator eit = als.endDistances.getIterator(); eit.hasMoreStrings();) {
					String e = eit.nextString();
					int ec = als.endDistances.getCount(e);
					endDistanceCountSquareSum += (ec * ec);
					System.out.print(e + " (" + als.endDistances.getCount(e) + ")" + (eit.hasMoreStrings() ? ", " : ""));
				}
				System.out.println();
				float endAlignmentScore = (((float) endDistanceCountSquareSum) / als.endDistances.getElementCount());
				if (als.firstNameStyles.contains(fullNameFNS))
					endAlignmentScore /= 2;
				if (!als.namePartOrders.contains(lastFirstNPO))
					endAlignmentScore /= 2;
				System.out.println("   --> score: " + endAlignmentScore);
				
				if ((als.instanceCount * 2) < bibRefs.length) {
					endAlignmentScore = ((endAlignmentScore * als.instanceCount) / bibRefs.length);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> few instance penalty, score set to: " + endAlignmentScore);
				}
				else if ((bibRefs.length * 2) < als.instanceCount) {
					endAlignmentScore = ((endAlignmentScore * bibRefs.length) / als.instanceCount);
					if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("   --> many instance penalty, score set to: " + endAlignmentScore);
				}
				
				als.alignmentScore = Math.max(startAlignmentScore, endAlignmentScore);
				als.isLeading = (endAlignmentScore < startAlignmentScore);
			}
			
			
			if ((als.refIDs.size() * 3) < bibRefs.length) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> too few references covered");
				continue;
			}
			
			if ((als.instanceCount * 3) < bibRefs.length) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> too few instances");
				continue;
			}
			
			if (authorListStyle == null) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> OK for starters");
				continue;
			}
			
			if (authorListStyle.alignmentScore < als.alignmentScore) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> new top style");
				continue;
			}
			else if (authorListStyle.alignmentScore > als.alignmentScore) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> worse than current style");
				continue;
			}
			
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> same as current style");
			if (als.nameCount > authorListStyle.nameCount) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> new top style for more names");
				continue;
			}
			else if (als.nameCount < authorListStyle.nameCount) {
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> fewer names than current style");
				continue;
			}
			
			if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> same number of names as current style");
			if (als.namePartOrders.size() < authorListStyle.namePartOrders.size()) {
				authorListStyle = als;
				if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> new top style for fewer name part orders");
				continue;
			}
			else if (DEBUG_AUTHOR_LIST_ASSEMBLY) System.out.println("  ==> same or more name part orders");
			
			//	TODO maybe also consider number of bridged tokens, fewer = better
		}
		
		//	finally
		return authorListStyle;
	}
	
	private void filterAuthorLists(BibRef[] bibRefs, AuthorListStyle authorListStyle) {
		if (authorListStyle == null)
			return;
		
		System.out.println("Author lists style is " + authorListStyle.key + " with score " + authorListStyle.alignmentScore);
		System.out.println("Author lists alignment is " + (authorListStyle.isLeading ? "leading" : "tailing"));
		
		//	for volume references, check for editor list labels, and re-select author list style if no author lists match current style
		if (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRefs[0].annotation.getType())) {
			boolean reselectAuthorListStyle = false;
			
			//	assess editor lists
			for (int r = 0; r < bibRefs.length; r++) {
				if (bibRefs[r].preExistingStructure)
					continue;
				boolean gotLabeledEditorList = false;
				boolean gotCompatibleLabeledEditorList = false;
				for (int l = 0; l < bibRefs[r].authorLists.length; l++) {
					if (bibRefs[r].authorLists[l].hasEditorListLabel)
						gotLabeledEditorList = true;
					if (authorListStyle.isCompatible(bibRefs[r].authorLists[l])) {
						if (bibRefs[r].authorLists[l].hasEditorListLabel)
							gotCompatibleLabeledEditorList = true;
					}
				}
				if (gotLabeledEditorList && !gotCompatibleLabeledEditorList)
					reselectAuthorListStyle = true;
			}
			
			//	re-select style if necessary
			if (reselectAuthorListStyle) {
				authorListStyle = this.getAuthorListStyle(bibRefs);
				System.out.println("Reselected author list style as " + authorListStyle.key + " with score " + authorListStyle.alignmentScore);
				System.out.println("Author list alignment now is " + (authorListStyle.isLeading ? "leading" : "tailing"));
			}
		}
		
		//	sort out author lists
		for (int r = 0; r < bibRefs.length; r++) {
			if (bibRefs[r].preExistingStructure)
				continue;
			
			System.out.println("Filtering author lists in " + bibRefs[r].annotation.toXML());
			ArrayList authorLists = new ArrayList();
			ArrayList knownAuthorLists = new ArrayList();
			boolean gotLabeledEditorLists = false;
			for (int l = 0; l < bibRefs[r].authorLists.length; l++) {
				System.out.println(" - " + bibRefs[r].authorLists[l].annotation.getValue());
				if (authorListStyle.isCompatible(bibRefs[r].authorLists[l])) {
					if ((bibRefs.length < 3) && (authorLists.size() != 0)) {
						System.out.println("  ==> removed (too late in reference)");
						continue;
					}
					authorLists.add(bibRefs[r].authorLists[l]);
					if (repetitionMarkerSpecialType.equals(((Annotation) bibRefs[r].authorLists[l].authorNames.get(0)).getType())) {
						Annotation rm = ((Annotation) bibRefs[r].authorLists[l].authorNames.get(0));
						rm.changeTypeTo(AUTHOR_ANNOTATION_TYPE);
						rm.setAttribute(repetitionMarkerSpecialType, repetitionMarkerSpecialType);
					}
					if (bibRefs[r].authorLists[l].hasEditorListLabel)
						gotLabeledEditorLists = true;
					System.out.println("  ==> retained");
				}
				else if (((Annotation) bibRefs[r].authorLists[l].authorNames.get(0)).hasAttribute(knownAuthorMarker)) {
					knownAuthorLists.add(bibRefs[r].authorLists[l]);
					System.out.println("  ==> known, shelved");
				}
				else System.out.println("  ==> removed");
			}
			if (VOLUME_REFERENCE_ANNOTATION_TYPE.equals(bibRefs[r].annotation.getType())) {
				if (gotLabeledEditorLists)
					for (int l = 0; l < authorLists.size(); l++) {
						if (!((AuthorList) authorLists.get(l)).hasEditorListLabel)
							authorLists.remove(l--);
					}
			}
			else if (authorLists.isEmpty()) {
				authorLists.addAll(knownAuthorLists);
//				continue;
			}
			if (authorLists.size() < bibRefs[r].authorLists.length)
				bibRefs[r].authorLists = ((AuthorList[]) authorLists.toArray(new AuthorList[authorLists.size()]));
			
		}
	}
	
	private Annotation[] getYears(BibRef bibRef) {
		String currentYear = new SimpleDateFormat("yyyy").format(new Date());
		
		Annotation[] years = Gamta.extractAllMatches(bibRef.annotation, this.yearRegEx, false);
		ArrayList plausibleYears = new ArrayList();
		for (int y = 0; y < years.length; y++) {
			
			//	this one's in the future ...
			if (currentYear.compareTo(years[y].getValue()) < 0)
				continue;
			
			//	check if embedded in URL or DOI
			boolean inUrlOrDoi = false;
			for (int u = 0; u < bibRef.urls.length; u++)
				if (AnnotationUtils.overlaps(bibRef.urls[u], years[y])) {
					inUrlOrDoi = true;
					break;
				}
			for (int d = 0; d < bibRef.dois.length; d++)
				if (AnnotationUtils.overlaps(bibRef.dois[d], years[y])) {
					inUrlOrDoi = true;
					break;
				}
			if (inUrlOrDoi)
				continue;
			
			//	check if part of title
			boolean isTitleNumber = false;
			for (int i = years[y].getStartIndex(); i < years[y].getEndIndex(); i++)
				if (bibRef.titleNumberTokens.contains(new Integer(i))) {
					isTitleNumber = true;
					break;
				}
			if (isTitleNumber)
				continue;
			
			//	this one's OK
			years[y].changeTypeTo(YEAR_ANNOTATION_TYPE);
			plausibleYears.add(years[y]);
		}
		
		return ((Annotation[]) plausibleYears.toArray(new Annotation[plausibleYears.size()]));
	}
	
	private Annotation[] getPageNumbers(BibRef bibRef) {
		
		//	annotate tokens forbidden before page numbers
		Annotation[] pageNumberInvalidatorLeadingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsLeading, false);
		HashMap pageNumberInvalidatorsLeading = new HashMap();
		for (int i = 0; i < pageNumberInvalidatorLeadingAnnots.length; i++)
			pageNumberInvalidatorsLeading.put(new Integer(pageNumberInvalidatorLeadingAnnots[i].getStartIndex()), pageNumberInvalidatorLeadingAnnots[i]);
		
		//	annotate tokens forbidden after page numbers
		Annotation[] pageNumberInvalidatorTailingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsTailing, false);
		HashMap pageNumberInvalidatorsTailing = new HashMap();
		for (int i = 0; i < pageNumberInvalidatorTailingAnnots.length; i++)
			pageNumberInvalidatorsTailing.put(new Integer(pageNumberInvalidatorTailingAnnots[i].getStartIndex()), pageNumberInvalidatorTailingAnnots[i]);
		
		//	get candidate page numbers
		Annotation[] pageNumberAnnots = Gamta.extractAllMatches(bibRef.annotation, this.pageRegEx, false);
		ArrayList pageNumbers = new ArrayList();
		ArrayList securePageNumbers = new ArrayList();
		for (int n = 0; n < pageNumberAnnots.length; n++) {
			pageNumberAnnots[n].changeTypeTo(PAGE_NUMBER_TYPE);
			
			//	this one is actually the index number of the reference string ...
			if (pageNumberAnnots[n].getStartIndex() == 0)
				continue;
			
			//	this one is part of some range, do not mark separately
			if ((pageNumberAnnots[n].getStartIndex() != 0) && "-".equals(bibRef.annotation.valueAt(pageNumberAnnots[n].getStartIndex() - 1)))
				continue;
			else if ((pageNumberAnnots[n].getEndIndex() < bibRef.annotation.size()) && "-".equals(bibRef.annotation.valueAt(pageNumberAnnots[n].getEndIndex())))
				continue;
			
			//	this one is secure
			if (!Gamta.isNumber(pageNumberAnnots[n].firstValue())) {
				pageNumbers.add(pageNumberAnnots[n]);
				securePageNumbers.add(pageNumberAnnots[n]);
				continue;
			}
			
			//	check if embedded in URL or DOI
			boolean inUrlOrDoi = false;
			for (int u = 0; u < bibRef.urls.length; u++)
				if (AnnotationUtils.overlaps(bibRef.urls[u], pageNumberAnnots[n])) {
					inUrlOrDoi = true;
					break;
				}
			for (int d = 0; d < bibRef.dois.length; d++)
				if (AnnotationUtils.overlaps(bibRef.dois[d], pageNumberAnnots[n])) {
					inUrlOrDoi = true;
					break;
				}
			if (inUrlOrDoi)
				continue;
			
			//	check if part of title
			boolean isTitleNumber = false;
			for (int i = pageNumberAnnots[n].getStartIndex(); i < pageNumberAnnots[n].getEndIndex(); i++)
				if (bibRef.titleNumberTokens.contains(new Integer(i))) {
					isTitleNumber = true;
					break;
				}
			if (isTitleNumber)
				continue;
			
			//	check if page number invalidated by token before it
			Annotation invalidatorLeading = ((Annotation) pageNumberInvalidatorsLeading.get(new Integer(pageNumberAnnots[n].getStartIndex()-1)));
			if (invalidatorLeading != null)
				continue;
			
			//	check if page number invalidated by token after it
			Annotation invalidatorTailing = ((Annotation) pageNumberInvalidatorsTailing.get(new Integer(pageNumberAnnots[n].getEndIndex())));
			if (invalidatorTailing == null)
				pageNumbers.add(pageNumberAnnots[n]);
			
			//	remember info to referenced publication being a book
			else if (this.bookContentHintNumberingInvalidatorsTailing.containsIgnoreCase(invalidatorTailing.getValue())) {
				if (DEBUG) System.out.println("Found book content hint: " + pageNumberAnnots[n] + " " + invalidatorTailing);
//				bibRef.gotBookContentHint = true;
				bibRef.bookContentInfos.add(Gamta.newAnnotation(bibRef.annotation, BOOK_CONTENT_INFO_ANNOTATION_TYPE, pageNumberAnnots[n].getStartIndex(), (invalidatorTailing.getEndIndex() - pageNumberAnnots[n].getStartIndex())));
			}
		}
		
		//	we have labelled page numbers, return only those
		if (!securePageNumbers.isEmpty() && (securePageNumbers.size() < pageNumbers.size()))
			return ((Annotation[]) securePageNumbers.toArray(new Annotation[securePageNumbers.size()]));
		
		//	we have only plain page numbers
		else return ((Annotation[]) pageNumbers.toArray(new Annotation[pageNumbers.size()]));
	}
	
	private Annotation[] getPageRanges(BibRef bibRef) {
		Annotation[] pageRanges =  this.getArabicPageRanges(bibRef);
		if (pageRanges.length == 0)
			pageRanges = this.getRomanPageRanges(bibRef);
		return pageRanges;
	}
	
	private Annotation[] getArabicPageRanges(BibRef bibRef) {
		Annotation[] pageRangeAnnots = Gamta.extractAllMatches(bibRef.annotation, this.pageRangeArabicRegEx, false);
		ArrayList pageRanges = new ArrayList();
		for (int r = 0; r < pageRangeAnnots.length; r++) {
			if (DEBUG) System.out.println("Checking possible page range: " + pageRangeAnnots[r].getValue());
			boolean inUrlOrDoiOrTitleNumber = false;
			
			//	check if embedded in URL or DOI
			for (int u = 0; u < bibRef.urls.length; u++)
				if (AnnotationUtils.overlaps(bibRef.urls[u],pageRangeAnnots[r])) {
					inUrlOrDoiOrTitleNumber = true;
					if (DEBUG) System.out.println(" --> overtlaps with URL");
					break;
				}
			for (int d = 0; d < bibRef.dois.length; d++)
				if (AnnotationUtils.overlaps(bibRef.dois[d], pageRangeAnnots[r])) {
					inUrlOrDoiOrTitleNumber = true;
					if (DEBUG) System.out.println(" --> overtlaps with DOI");
					break;
				}
			
			//	check overlap with title numbers
			for (int t = pageRangeAnnots[r].getStartIndex(); t < pageRangeAnnots[r].getEndIndex(); t++)
				if (bibRef.titleNumberTokens.contains(new Integer(t))) {
					inUrlOrDoiOrTitleNumber = true;
					if (DEBUG) System.out.println(" --> overtlaps with title number");
					break;
				}
			
			if (inUrlOrDoiOrTitleNumber)
				continue;
			
			//	check if second number larger than first (numbers with dashes can also occur in identifiers, etc.)
			String firstNumber = null;
			String secondNumber = null;
			for (int t = 0; t < pageRangeAnnots[r].size(); t++)
				if (Gamta.isNumber(pageRangeAnnots[r].valueAt(t))) {
					if (firstNumber == null)
						firstNumber = pageRangeAnnots[r].valueAt(t);
					else if (secondNumber == null)
						secondNumber = pageRangeAnnots[r].valueAt(t);
				}
			
			//	too few numbers
			if (secondNumber == null) {
				if (DEBUG) System.out.println(" --> second number invalid");
				continue;
			}
			
			//	fill in omitted positions in second number
			if (secondNumber.length() < firstNumber.length())
				secondNumber = (firstNumber.substring(0, (firstNumber.length() - secondNumber.length())) + secondNumber);
			
			//	compare numerically
			if (Integer.parseInt(secondNumber) <= Integer.parseInt(firstNumber)) {
				if (DEBUG) System.out.println(" --> second number less than first");
				continue;
			}
			
			//	this one's OK
			pageRangeAnnots[r].changeTypeTo(PAGE_RANGE_ANNOTATION_TYPE);
			pageRanges.add(pageRangeAnnots[r]);
			if (DEBUG) System.out.println(" ==> got candidate page range: " + pageRangeAnnots[r].toXML());
		}
		
		return ((Annotation[]) pageRanges.toArray(new Annotation[pageRanges.size()]));
	}
	
	private Annotation[] getRomanPageRanges(BibRef bibRef) {
		Annotation[] pageRangeAnnots = Gamta.extractAllMatches(bibRef.annotation, this.pageRangeRomanRegEx, false);
		ArrayList pageRanges = new ArrayList();
		for (int r = 0; r < pageRangeAnnots.length; r++) {
			
			//	check if embedded in URL or DOI
			boolean inUrlOrDoi = false;
			for (int u = 0; u < bibRef.urls.length; u++)
				if (AnnotationUtils.overlaps(bibRef.urls[u],pageRangeAnnots[r])) {
					inUrlOrDoi = true;
					break;
				}
			for (int d = 0; d < bibRef.dois.length; d++)
				if (AnnotationUtils.overlaps(bibRef.dois[d], pageRangeAnnots[r])) {
					inUrlOrDoi = true;
					break;
				}
			if (inUrlOrDoi)
				continue;
			
			//	check if second number larger than first (numbers with dashes can also occur in identifiers, etc.)
			String firstNumber = null;
			String secondNumber = null;
			for (int t = 0; t < pageRangeAnnots[r].size(); t++)
				if (pageRangeAnnots[r].valueAt(t).matches(this.romanNumberRegEx)) {
					if (firstNumber == null)
						firstNumber = pageRangeAnnots[r].valueAt(t);
					else if (secondNumber == null)
						firstNumber = pageRangeAnnots[r].valueAt(t);
				}
			
			//	got two numbers?
			if (secondNumber != null) try {
				
				//	compare numerically
				if (Gamta.parseRomanNumber(secondNumber) <= Gamta.parseRomanNumber(firstNumber))
					continue;
				
				//	this one's OK
				pageRangeAnnots[r].changeTypeTo(PAGE_RANGE_ANNOTATION_TYPE);
				pageRanges.add(pageRangeAnnots[r]);
			}
			
			//	we have to catch that number format exception, just in case ...
			catch (Exception e) {}
		}
		
		return ((Annotation[]) pageRanges.toArray(new Annotation[pageRanges.size()]));
	}
	
	private void markTitleNumbers(BibRef bibRef) {
		for (int p = 0; p < this.titleNumberPatterns.size(); p++) {
			Annotation[] titleNumberAnnots = Gamta.extractAllMatches(bibRef.annotation, this.titleNumberPatterns.get(p), false);
			for (int t = 0; t < titleNumberAnnots.length; t++) {
				if (DEBUG) System.out.println("Got title number [ " + this.titleNumberPatterns.get(p) + " ]: " + titleNumberAnnots[t].getValue());
				for (int i = titleNumberAnnots[t].getStartIndex(); i < titleNumberAnnots[t].getEndIndex(); i++)
					bibRef.titleNumberTokens.add(new Integer(i));
			}
		}
	}
	
	private Annotation[] getPartDesignators(BibRef bibRef) {
		
		//	annotate tokens forbidden before part designators
		Annotation[] partDesignatorInvalidatorLeadingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsLeading, false);
		HashMap partDesignatorInvalidatorsLeading = new HashMap();
		for (int i = 0; i < partDesignatorInvalidatorLeadingAnnots.length; i++)
			partDesignatorInvalidatorsLeading.put(new Integer(partDesignatorInvalidatorLeadingAnnots[i].getStartIndex()), partDesignatorInvalidatorLeadingAnnots[i]);
		
		//	annotate tokens forbidden after part designators
		Annotation[] partDesignatorInvalidatorTailingAnnots = Gamta.extractAllContained(bibRef.annotation, this.numberingInvalidatorsTailing, false);
		HashMap partDesignatorInvalidatorsTailing = new HashMap();
		for (int i = 0; i < partDesignatorInvalidatorTailingAnnots.length; i++)
			partDesignatorInvalidatorsTailing.put(new Integer(partDesignatorInvalidatorTailingAnnots[i].getStartIndex()), partDesignatorInvalidatorTailingAnnots[i]);
		
		//	get part designators
		Annotation[] partDesignatorAnnots = Gamta.extractAllMatches(bibRef.annotation, this.partDesignatorRegEx, false);
		ArrayList partDesignators = new ArrayList();
		ArrayList securePartDesignators = new ArrayList();
		for (int p = 0; p < partDesignatorAnnots.length; p++) {
			if (DEBUG) System.out.println("Found possible part designator: " + partDesignatorAnnots[p].getValue());
			
			//	this one is likely a reference number, not a part designator
			if (partDesignatorAnnots[p].getStartIndex() == 0) {
				if (DEBUG) System.out.println(" --> at start, ignoring");
				continue;
			}
			
			//	set annotation type
			partDesignatorAnnots[p].changeTypeTo(PART_DESIGNATOR_ANNOTATION_TYPE);
			
			//	this one is part of some range, do not mark separately
			if ("-".equals(bibRef.annotation.valueAt(partDesignatorAnnots[p].getStartIndex() - 1))) {
				if (DEBUG) System.out.println(" --> after dash, ignoring");
				continue;
			}
			else if ((partDesignatorAnnots[p].getEndIndex() < bibRef.annotation.size()) && "-".equals(bibRef.annotation.valueAt(partDesignatorAnnots[p].getEndIndex()))) {
				if (DEBUG) System.out.println(" --> before dash, ignoring");
				continue;
			}
			
			//	check if embedded in URL or DOI
			boolean inUrlOrDoi = false;
			for (int u = 0; u < bibRef.urls.length; u++)
				if (AnnotationUtils.overlaps(bibRef.urls[u], partDesignatorAnnots[p])) {
					inUrlOrDoi = true;
					break;
				}
			for (int d = 0; d < bibRef.dois.length; d++)
				if (AnnotationUtils.overlaps(bibRef.dois[d], partDesignatorAnnots[p])) {
					inUrlOrDoi = true;
					break;
				}
			if (inUrlOrDoi) {
				if (DEBUG) System.out.println(" --> in URL/DOI, ignoring");
				continue;
			}
			
			//	check if part of title
			boolean isTitleNumber = false;
			for (int i = partDesignatorAnnots[p].getStartIndex(); i < partDesignatorAnnots[p].getEndIndex(); i++)
				if (bibRef.titleNumberTokens.contains(new Integer(i))) {
					isTitleNumber = true;
					break;
				}
			if (isTitleNumber) {
				if (DEBUG) System.out.println(" --> title number, ignoring");
				continue;
			}
			
			//	this one is secure
			if (!Gamta.isNumber(partDesignatorAnnots[p].firstValue()) && !Gamta.isRomanNumber(partDesignatorAnnots[p].firstValue()) && (partDesignatorAnnots[p].firstValue().length() > 1)) {
				partDesignators.add(partDesignatorAnnots[p]);
				securePartDesignators.add(partDesignatorAnnots[p]);
				if (DEBUG) System.out.println(" ==> secure part designator");
				continue;
			}
			
			//	check if part designators invalidated by token before it
			Annotation invalidatorLeading = ((Annotation) partDesignatorInvalidatorsLeading.get(new Integer(partDesignatorAnnots[p].getStartIndex()-1)));
			if (invalidatorLeading != null) {
				if (DEBUG) System.out.println(" --> invalidated by leading '" + bibRef.annotation.valueAt(partDesignatorAnnots[p].getStartIndex()-1) + "'");
				continue;
			}
			
			//	check if part designators invalidated by token after it
			Annotation invalidatorTailing = ((Annotation) partDesignatorInvalidatorsTailing.get(new Integer(partDesignatorAnnots[p].getEndIndex())));
			if (invalidatorTailing != null) {
				if (DEBUG) System.out.println(" --> invalidated by tailing '" + bibRef.annotation.valueAt(partDesignatorAnnots[p].getEndIndex()) + "'");
				
				//	remember hint to referenced publication being a book
				if (this.bookContentHintNumberingInvalidatorsTailing.containsIgnoreCase(invalidatorTailing.getValue())) {
					if (DEBUG) System.out.println("Found book content hint: " + partDesignatorAnnots[p] + " " + invalidatorTailing);
					bibRef.bookContentInfos.add(Gamta.newAnnotation(bibRef.annotation, BOOK_CONTENT_INFO_ANNOTATION_TYPE, partDesignatorAnnots[p].getStartIndex(), (invalidatorTailing.getEndIndex() - partDesignatorAnnots[p].getStartIndex())));
				}
				continue;
			}
			
			//	ignore unlabeled letters and Roman numbers
			if (!Gamta.isNumber(partDesignatorAnnots[p].firstValue()) && !Gamta.isRomanNumber(partDesignatorAnnots[p].firstValue())) {
				if (DEBUG) System.out.println(" --> ingored as standalone letter");
				continue;
			}
			
			//	hold on to this one
			if (DEBUG) System.out.println(" ==> possible part designator");
			partDesignators.add(partDesignatorAnnots[p]);
		}
		
		//	we have labelled part designators, return only those
		if (!securePartDesignators.isEmpty() && (securePartDesignators.size() < partDesignators.size()))
			partDesignatorAnnots = ((Annotation[]) securePartDesignators.toArray(new Annotation[securePartDesignators.size()]));
		
		//	we have only plain part designators
		else partDesignatorAnnots = ((Annotation[]) partDesignators.toArray(new Annotation[partDesignators.size()]));
//		
//		//	make sure numerical part designators are preferred over letters in structure vote
//		Arrays.sort(partDesignatorAnnots, new Comparator() {
//			public int compare(Object o1, Object o2) {
//				Annotation pd1 = ((Annotation) o1);
//				Annotation pd2 = ((Annotation) o2);
//				if (Gamta.isNumber(pd1.lastValue()) == Gamta.isNumber(pd2.lastValue()))
//					return pd1.compareTo(pd2);
//				else if (Gamta.isNumber(pd1.lastValue()))
//					return -1;
//				else return 1;
//			}
//		});
		
		//	finally ...
		return partDesignatorAnnots;
	}
	
	private void classifyPartDesignators(BibRef bibRef) {
		
		//	nothing to classify
		if ((bibRef.partDesignators == null) || (bibRef.partDesignators.length == 0))
			return;
		
		//	get hints
		Annotation[] partDesignatorHints = Gamta.extractAllContained(bibRef.annotation, this.partDesignatorHints, false);
		for (int h = 0; h < partDesignatorHints.length; h++) {
			String partDesignatorHint = TokenSequenceUtils.concatTokens(partDesignatorHints[h], true, true);
			String partDesignatorType = null;
			if (this.volumeDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = VOLUME_DESIGNATOR_TYPE;
			else if (this.issueDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = ISSUE_DESIGNATOR_TYPE;
			else if (this.numberDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = NUMBER_DESIGNATOR_TYPE;
			else if (this.fascicleDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = FASCICLE_DESIGNATOR_TYPE;
			else if (this.seriesDesignatorHints.containsIgnoreCase(partDesignatorHint))
				partDesignatorType = SERIES_DESIGNATOR_TYPE;
			if (partDesignatorType != null) {
				partDesignatorHints[h].setAttribute(TYPE_ATTRIBUTE, partDesignatorType);
				bibRef.partDesignatorHints.put(new Integer(partDesignatorHints[h].getEndIndex()), partDesignatorHints[h]);
			}
		}
		
		//	exploit hints
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			Annotation partDesignatorHint = ((Annotation) bibRef.partDesignatorHints.get(new Integer(bibRef.partDesignators[p].getStartIndex())));
			if (partDesignatorHint != null) {
//				if (SERIES_DESIGNATOR_TYPE.equals(partDesignatorHint.getAttribute(TYPE_ATTRIBUTE))) {
//					if (bibRef.partDesignators[p].length() < 2)
//						bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, partDesignatorHint.getAttribute(TYPE_ATTRIBUTE));
//				}
//				else bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, partDesignatorHint.getAttribute(TYPE_ATTRIBUTE));
				bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, partDesignatorHint.getAttribute(TYPE_ATTRIBUTE));
			}
			else if (bibRef.partDesignators[p].size() == 1) {
				String partDesignator = bibRef.partDesignators[p].firstValue();
				if (partDesignator.matches("[A-Z]"))
					bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, SERIES_DESIGNATOR_TYPE);
				else if (partDesignator.matches("[IVXivx]+"))
					bibRef.partDesignators[p].setAttribute(TYPE_ATTRIBUTE, FASCICLE_DESIGNATOR_TYPE);
			}
		}
		
		//	collect part types already used
		HashSet usedPartDesignatorTypes = new HashSet();
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			if (bibRef.partDesignators[p].hasAttribute(TYPE_ATTRIBUTE))
				usedPartDesignatorTypes.add(bibRef.partDesignators[p].getAttribute(TYPE_ATTRIBUTE));
		}
		
		//	sort out classified part designators, check brackets for rest
		ArrayList classified = new ArrayList();
		ArrayList noBrackets = new ArrayList();
		ArrayList inBrackets = new ArrayList();
		for (int p = 0; p < bibRef.partDesignators.length; p++) {
			
			//	we're already sure about this one
			if (bibRef.partDesignators[p].hasAttribute(TYPE_ATTRIBUTE)) {
				classified.add(bibRef.partDesignators[p]);
				continue;
			}
			
			//	no room for brackets
			if ((bibRef.partDesignators[p].getStartIndex() == 0) || (bibRef.partDesignators[p].getEndIndex() == bibRef.annotation.size())) {
				noBrackets.add(bibRef.partDesignators[p]);
				continue;
			}
			
			//	inspect tokens before and after
			String before = bibRef.annotation.valueAt(bibRef.partDesignators[p].getStartIndex()-1);
			String after = bibRef.annotation.valueAt(bibRef.partDesignators[p].getEndIndex());
			if (")".equals(after) && ("(".equals(before) || bibRef.partDesignatorHints.containsKey(new Integer(bibRef.partDesignators[p].getStartIndex()))))
				inBrackets.add(bibRef.partDesignators[p]);
			else noBrackets.add(bibRef.partDesignators[p]);
		}
		
		//	we have an explicit volume number, make ones in brackets issues (choose later, after journal marked
		if (usedPartDesignatorTypes.contains(VOLUME_DESIGNATOR_TYPE)) {
			for (int i = 0; i < inBrackets.size(); i++)
				((Annotation) inBrackets.get(i)).setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
		}
		
		//	we have a likely volume number, make ones in brackets issues (choose later, after journal marked
		else if (noBrackets.size() != 0) {
			for (int i = 0; i < inBrackets.size(); i++)
				((Annotation) inBrackets.get(i)).setAttribute(TYPE_ATTRIBUTE, ISSUE_DESIGNATOR_TYPE);
			for (int n = 0; n < noBrackets.size(); n++)
				((Annotation) noBrackets.get(n)).setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
		}
		
		//	only part designators in brackets, make them volume numbers
		else for (int i = 0; i < inBrackets.size(); i++)
			((Annotation) inBrackets.get(i)).setAttribute(TYPE_ATTRIBUTE, VOLUME_DESIGNATOR_TYPE);
		
		//	report
		if (DEBUG) {
			System.out.println("Classified part designators in " + bibRef.annotation.toXML());
			for (int p = 0; p < bibRef.partDesignators.length; p++)
				System.out.println(" - " + bibRef.partDesignators[p].toXML());
		}
	}
	
	void trimPunctuation(MutableAnnotation[] bibRefs) {
		
		//	truncate leading and tailing punctuation from detail annotations
		for (int r = 0; r < bibRefs.length; r++) {
			this.truncatePunctuation(bibRefs[r], AUTHOR_ANNOTATION_TYPE, "", ".");
			this.truncatePunctuation(bibRefs[r], TITLE_ANNOTATION_TYPE, "(", "?!).");
			this.truncatePunctuation(bibRefs[r], YEAR_ANNOTATION_TYPE, "", "");
			if (detailOrigin) {
				this.truncatePunctuation(bibRefs[r], JOURNAL_NAME_ANNOTATION_TYPE, "", ".");
				this.truncatePunctuation(bibRefs[r], PUBLISHER_ANNOTATION_TYPE, "", ".");
				this.truncatePunctuation(bibRefs[r], LOCATION_ANNOTATION_TYPE, "", ".");
				this.truncatePunctuation(bibRefs[r], VOLUME_TITLE_ANNOTATION_TYPE, "(", "?!).");
			}
			else this.truncatePunctuation(bibRefs[r], JOURNAL_NAME_OR_PUBLISHER_ANNOTATION_TYPE, "", ".");
			this.truncatePunctuation(bibRefs[r], PART_DESIGNATOR_ANNOTATION_TYPE, "", "");
			this.truncatePunctuation(bibRefs[r], PAGINATION_ANNOTATION_TYPE, "", "");
			this.truncatePunctuation(bibRefs[r], EDITOR_ANNOTATION_TYPE, "", ".");
			this.truncatePunctuation(bibRefs[r], VOLUME_TITLE_ANNOTATION_TYPE, "(", "?!).");
		}
	}
	
	private void truncatePunctuation(MutableAnnotation bibRef, String detailType, String retainStart, String retainEnd) {
		MutableAnnotation[] details = bibRef.getMutableAnnotations(detailType);
		for (int d = 0; d < details.length; d++) {
			MutableAnnotation detail = details[d];
			if ((d == 0) && AUTHOR_ANNOTATION_TYPE.equals(detailType) && details[0].hasAttribute(repetitionMarkerSpecialType))
				continue;
			
			//	truncate end first, as punctuation marks amass there more likely than at the start
			int end = details[d].size();
			while (end > 0) {
				String eValue = detail.valueAt(end-1);
				if (Gamta.PUNCTUATION.indexOf(eValue) == -1)
					break;
				if (retainEnd.indexOf(eValue) != -1)
					break;
				if (Gamta.isClosingBracket(eValue)) {
					boolean gotOpening = false;
					for (int l = (end-1); l > 1; l--)
						if (Gamta.opens(detail.valueAt(l-1), eValue)) {
							gotOpening = true;
							break;
						}
					if (gotOpening)
						break;
				}
				end--;
			}
			
			int start = 0;
			while (start < end) {
				String sValue = detail.valueAt(start);
				if (Gamta.PUNCTUATION.indexOf(sValue) == -1)
					break;
				if (retainStart.indexOf(sValue) != -1)
					break;
				if (Gamta.isOpeningBracket(sValue)) {
					boolean gotClosing = false;
					for (int l = (start+1); l < (end - 1); l++)
						if (Gamta.closes(detail.valueAt(l), sValue)) {
							gotClosing = true;
							break;
						}
					if (gotClosing)
						break;
				}
				start++;
			}
			
			if ((start > 0) || (end < detail.size())) {
				if (start < end) {
					MutableAnnotation newDetail = detail.addAnnotation(detailType, start, (end - start));
					newDetail.copyAttributes(detail);
					details[d] = newDetail;
				}
				bibRef.removeAnnotation(detail);
			}
		}
	}
	
	//	clean up duplicate details
	void removeDuplicateDetails(MutableAnnotation data) {
		for (int t = 0; t < this.relevantTypes.size(); t++)
			AnnotationFilter.removeDuplicates(data, this.relevantTypes.get(t));
		AnnotationFilter.removeDuplicates(data, EDITOR_ANNOTATION_TYPE);
		AnnotationFilter.removeDuplicates(data, VOLUME_TITLE_ANNOTATION_TYPE);
	}
	
	//	add detail attributes & learn
	void setDetailAttributes(MutableAnnotation[] bibRefs) {
		Properties transferDetails = new Properties();
		for (int r = 0; r < bibRefs.length; r++)
			if (bibRefs[r].hasAttribute(GOT_FEEDBACK_ATTRIBUTE)) {
				this.setDetailAttributes(bibRefs[r], transferDetails);
				this.learnDetails(bibRefs[r]);
			}
	}
	private void setDetailAttributes(MutableAnnotation bibRef, Properties transferDetails) {
		MutableAnnotation[] details;
		for (int t = 0; t < this.relevantTypes.size(); t++) {
			String detailType = this.relevantTypes.get(t);
			details = bibRef.getMutableAnnotations(detailType);
			String detail = null;
			
//			//	prevent second author from being used if first author is omitted (replaced by repetition sign before first author given explicitly)
//			if (AUTHOR_ANNOTATION_TYPE.equals(detailType) && (details.length != 0) && (details[0].getStartIndex() != 0)) {
//				String beforeFirstAuthor = bibRef.valueAt(details[0].getStartIndex() - 1);
//				if (this.authorListSeparators.contains(beforeFirstAuthor) && (".,".indexOf(beforeFirstAuthor) == -1))
//					details = new MutableAnnotation[0];
//			}
			//	with repetition sign, make way for transfer
			if (AUTHOR_ANNOTATION_TYPE.equals(detailType)) {
				while ((details.length != 0) && details[0].hasAttribute(repetitionMarkerSpecialType)) {
					MutableAnnotation[] nDetails = new MutableAnnotation[details.length - 1];
					System.arraycopy(details, 1, nDetails, 0, nDetails.length);
					if (detail == null) {
						detail = transferDetails.getProperty(detailType);
						details[0].setAttribute(REPEATED_AUTHORS_ATTRIBUTE, detail);
					}
					details = nDetails;
				}
			}
			
			//	remove whitespace from DOIs and URLs
			if (PUBLICATION_DOI_ANNOTATION_TYPE.equals(detailType) || PUBLICATION_URL_ANNOTATION_TYPE.equals(detailType)) {
				for (int d = 0; d < details.length; d++) {
					for (int w = 0; w < (details[d].size()-1); w++)
						details[d].setWhitespaceAfter("", w);
				}
				
				//	set URL attribute
				if (details.length != 0) {
					detail = TokenSequenceUtils.concatTokens(details[0], false, true);
					if (PUBLICATION_DOI_ANNOTATION_TYPE.equals(detailType) && detail.toLowerCase().startsWith("doi:"))
						detail = "http://dx.doi.org/" + detail.substring("doi:".length());
					bibRef.setAttribute(CITED_PUBLICATION_URL_ATTRIBUTE, detail);
				}
			}
			
			//	get and store detail string, reusing ones from previous references if not given explicitly
			else {
				
				//	concatenate authors and editors with separating ' & '
				if (AUTHOR_ANNOTATION_TYPE.equals(detailType) || EDITOR_ANNOTATION_TYPE.equals(detailType)) {
					for (int d = 0; d < details.length; d++) {
						if (detail != null)
							detail += (" & " + TokenSequenceUtils.concatTokens(details[d], true, true));
						else detail = TokenSequenceUtils.concatTokens(details[d], true, true);
					}
					
					//	get author from transfer list if omitted completely (not editors, though, as many references do not include or imply any)
					if ((detail == null) && AUTHOR_ANNOTATION_TYPE.equals(detailType))
						detail = transferDetails.getProperty(detailType);
				}
				
				//	use only first token for year
				else if (YEAR_ANNOTATION_TYPE.equals(detailType)) detail = ((details.length == 0) ? transferDetails.getProperty(detailType) : details[0].firstValue());
				
				//	use only first value for all other elements
				else detail = ((details.length == 0) ? transferDetails.getProperty(detailType) : TokenSequenceUtils.concatTokens(details[0], true, true));
				
				//	store whatever we have
				if (detail != null) {
					bibRef.setAttribute(detailType, detail);
					if (this.transferableTypes.contains(detailType))
						transferDetails.setProperty(detailType, detail);
				}
			}
		}
		
		//	handle volume reference details
		details = bibRef.getMutableAnnotations(EDITOR_ANNOTATION_TYPE);
		if (details.length != 0)
			bibRef.setAttribute(EDITOR_ANNOTATION_TYPE, TokenSequenceUtils.concatTokens(details[0], true, true));
		details = bibRef.getMutableAnnotations(VOLUME_TITLE_ANNOTATION_TYPE);
		if (details.length != 0)
			bibRef.setAttribute(VOLUME_TITLE_ANNOTATION_TYPE, TokenSequenceUtils.concatTokens(details[0], true, true));
	}
	
	MutableAnnotation[] getFeedback(MutableAnnotation data, MutableAnnotation[] bibRefs, boolean allowRemove, boolean allowSplit) {
		
		//	find IDs of paragraphs surrounding the references
		Properties bibRefParagraphIDs = new Properties();
		MutableAnnotation[] paragraphs = data.getMutableAnnotations(PARAGRAPH_TYPE);
		int paragraphIndex = 0;
		for (int r = 0; r < bibRefs.length; r++) {
			
			//	find next possible containing paragraph
			while ((paragraphIndex < paragraphs.length) && (paragraphs[paragraphIndex].getEndIndex() <= bibRefs[r].getStartIndex()))
				paragraphIndex++;
			
			//	found containing paragraph, map IDs and add page number attribute
			if ((paragraphIndex < paragraphs.length) && AnnotationUtils.contains(paragraphs[paragraphIndex], bibRefs[r])) {
				bibRefParagraphIDs.setProperty(bibRefs[r].getAnnotationID(), paragraphs[paragraphIndex].getAnnotationID());
				bibRefs[r].setAttribute(PAGE_ID_ATTRIBUTE, paragraphs[paragraphIndex].getAttribute(PAGE_ID_ATTRIBUTE));
				bibRefs[r].setAttribute(PAGE_NUMBER_ATTRIBUTE, paragraphs[paragraphIndex].getAttribute(PAGE_NUMBER_ATTRIBUTE));
			}
		}
		
		//	prepare feedback dialogs
		BibRefParserFeedbackPanel[] brpfps = new BibRefParserFeedbackPanel[bibRefs.length];
		for (int r = 0; r < bibRefs.length; r++)
			brpfps[r] = this.getFeedbackPanel(bibRefs[r], data.getDocumentProperty(DOCUMENT_ID_ATTRIBUTE), bibRefParagraphIDs, allowRemove, allowSplit);
		
		//	can we issue all dialogs at once?
		if (FeedbackPanel.isMultiFeedbackEnabled()) {
			FeedbackPanel.getMultiFeedback(brpfps);
			
			//	process all feedback data together
			for (int d = 0; d < brpfps.length; d++) {
				brpfps[d].writeChanges(bibRefs[d]);
				bibRefs[d].setAttribute(PUBLICATION_TYPE_ATTRIBUTE, brpfps[d].getBibRefType().name);
				if (brpfps[d].noBibRef.isSelected())
					bibRefs[d].setAttribute(NO_BIB_REF_ATTRIBUTE, NO_BIB_REF_ATTRIBUTE);
				else bibRefs[d].removeAttribute(NO_BIB_REF_ATTRIBUTE);
				bibRefs[d].setAttribute(GOT_FEEDBACK_ATTRIBUTE, GOT_FEEDBACK_ATTRIBUTE);
			}
		}
		
		//	display dialogs one by one otherwise (allow cancel in the middle)
		else for (int d = 0; d < brpfps.length; d++) {
			if (d != 0)
				brpfps[d].addButton("Previous");
			brpfps[d].addButton("Cancel");
			brpfps[d].addButton("OK" + (((d+1) == brpfps.length) ? "" : " & Next"));
			
			String aefpTitle = brpfps[d].getTitle();
			brpfps[d].setTitle(aefpTitle + " - (" + (d+1) + " of " + brpfps.length + ")");
			
			String f = brpfps[d].getFeedback();
			if (f == null)
				f = "Cancel";
			
			brpfps[d].setTitle(aefpTitle);
			
			//	current dialog submitted, process data
			if (f.startsWith("OK")) {
				brpfps[d].writeChanges(bibRefs[d]);
				bibRefs[d].setAttribute(TYPE_ATTRIBUTE, brpfps[d].getBibRefType().name);
				if (brpfps[d].noBibRef.isSelected())
					bibRefs[d].setAttribute(NO_BIB_REF_ATTRIBUTE, NO_BIB_REF_ATTRIBUTE);
				else bibRefs[d].removeAttribute(NO_BIB_REF_ATTRIBUTE);
				bibRefs[d].setAttribute(GOT_FEEDBACK_ATTRIBUTE, GOT_FEEDBACK_ATTRIBUTE);
			}
			
			//	back to previous dialog
			else if ("Previous".equals(f)) {
				bibRefs[d].removeAttribute(GOT_FEEDBACK_ATTRIBUTE);
				d-=2;
			}
			
			//	cancel from current dialog on
			else d = brpfps.length;
		}
		
		//	sort out references marked for removal, and split the ones marked for splitting
		ArrayList splitBibRefList = new ArrayList();
		for (int r = 0; r < bibRefs.length; r++) {
			if (!bibRefs[r].hasAttribute(GOT_FEEDBACK_ATTRIBUTE))
				continue;
			
			//	do remove if required
			if (bibRefs[r].hasAttribute(NO_BIB_REF_ATTRIBUTE)) {
				for (int t = 0; t < this.relevantTypes.size(); t++)
					AnnotationFilter.removeAnnotations(bibRefs[r], this.relevantTypes.get(t));
				AnnotationFilter.removeAnnotations(bibRefs[r], VOLUME_REFERENCE_ANNOTATION_TYPE);
				data.removeAnnotation(bibRefs[r]);
				continue;
			}
			
			//	check for splits
			Annotation[] splitMarkers = bibRefs[r].getAnnotations(NEXT_REFERENCE_ANNOTATION_TYPE);
			if (splitMarkers.length == 0)
				continue;
			
			//	get parent paragraph ID
			String paragraphId = bibRefParagraphIDs.getProperty(bibRefs[r].getAnnotationID(), "");
			
			//	cut original reference
			MutableAnnotation bibRef = data.addAnnotation(BIBLIOGRAPHIC_REFERENCE_TYPE, bibRefs[r].getStartIndex(), splitMarkers[0].getStartIndex());
			bibRef.copyAttributes(bibRefs[r]);
			bibRefParagraphIDs.setProperty(bibRef.getAnnotationID(), paragraphId);
			
			//	mark next reference
			for (int s = 0; s < splitMarkers.length; s++) {
				MutableAnnotation nextBibRef = data.addAnnotation(BIBLIOGRAPHIC_REFERENCE_TYPE, (bibRefs[r].getStartIndex() + splitMarkers[s].getStartIndex()), ((((s+1) == splitMarkers.length) ? bibRefs[r].size() : splitMarkers[s+1].getStartIndex()) - splitMarkers[s].getStartIndex()));
				nextBibRef.copyAttributes(bibRefs[r]);
				bibRefs[r].removeAttribute(GOT_FEEDBACK_ATTRIBUTE);
				nextBibRef.removeAttribute(GOT_FEEDBACK_ATTRIBUTE);
				bibRefParagraphIDs.setProperty(nextBibRef.getAnnotationID(), paragraphId);
				for (int t = 0; t < this.relevantTypes.size(); t++)
					AnnotationFilter.removeAnnotations(nextBibRef, this.relevantTypes.get(t));
				AnnotationFilter.removeAnnotations(nextBibRef, NEXT_REFERENCE_ANNOTATION_TYPE);
				splitBibRefList.add(nextBibRef);
				System.out.println("Got split reference: " + nextBibRef.toXML());
			}
			
			//	replace original reference
			data.removeAnnotation(bibRefs[r]);
			bibRefs[r] = bibRef;
		}
		
		//	no splits
		if (splitBibRefList.isEmpty())
			return null;
		
		//	return split references for further processing
		else return ((MutableAnnotation[]) splitBibRefList.toArray(new MutableAnnotation[splitBibRefList.size()]));
	}
	
	private BibRefParserFeedbackPanel getFeedbackPanel(MutableAnnotation bibRef, String docId, Properties bibRefParagraphIDs, boolean allowRemove, boolean allowSplit) {
		String titleExtension = "";
		BibRefParserFeedbackPanel brpfp = new BibRefParserFeedbackPanel("Check Bibliographic Reference Details" + titleExtension);
		brpfp.setLabel("<HTML>Please make sure that all the details of this bibliographic reference are marked correctly." +
				"<BR>If multiple bibliographic references are clung together, annotate the details of the first one normally," +
				"<BR>&nbsp;&nbsp;and annotate the first token of any subsequent one as <B>nextRef</B> to initiate a split." +
				"<BR>If it is not a bibliographic reference at all, check the <B>Not a Bibliographic Reference</B> to indicate so." +
				"</HTML>");
		for (int t = 0; t < this.relevantTypes.size(); t++) {
			String type = this.relevantTypes.get(t);
			Color color = this.getAnnotationHighlight(type);
			if (color != null)
				brpfp.addDetailType(type, color);
		}
		if (allowSplit)
			brpfp.addDetailType(NEXT_REFERENCE_ANNOTATION_TYPE, this.getAnnotationHighlight(NEXT_REFERENCE_ANNOTATION_TYPE));
		brpfp.setAllowRemove(allowRemove);
		brpfp.setAnnotation(bibRef);
		
		//	add reference types and preset selection
		brpfp.setBibRefTypes((BibRefType[]) this.referenceTypes.values().toArray(new BibRefType[this.referenceTypes.size()]));
		if (bibRef.hasAttribute(PUBLICATION_TYPE_ATTRIBUTE))
			brpfp.setBibRefType(new BibRefType((String) bibRef.getAttribute(PUBLICATION_TYPE_ATTRIBUTE, "")));
		
		//	add background information
		brpfp.setProperty(FeedbackPanel.TARGET_DOCUMENT_ID_PROPERTY, docId);
		brpfp.setProperty(FeedbackPanel.TARGET_PAGE_NUMBER_PROPERTY, ((String) bibRef.getAttribute(PAGE_NUMBER_ATTRIBUTE)));
		brpfp.setProperty(FeedbackPanel.TARGET_PAGE_ID_PROPERTY, ((String) bibRef.getAttribute(PAGE_ID_ATTRIBUTE)));
		brpfp.setProperty(FeedbackPanel.TARGET_ANNOTATION_ID_PROPERTY, bibRefParagraphIDs.getProperty(bibRef.getAnnotationID(), ""));
		brpfp.setProperty(FeedbackPanel.TARGET_ANNOTATION_TYPE_PROPERTY, BIBLIOGRAPHIC_REFERENCE_TYPE);
		
		//	add target page number
		brpfp.setProperty(FeedbackPanel.TARGET_PAGES_PROPERTY, ((String) bibRef.getAttribute(PAGE_NUMBER_ATTRIBUTE)));
		brpfp.setProperty(FeedbackPanel.TARGET_PAGE_IDS_PROPERTY, ((String) bibRef.getAttribute(PAGE_ID_ATTRIBUTE)));
		
		//	finally ...
		return brpfp;
	}
	
	/**
	 * Feedback panel for correcting parsed bibliographic references. Has to be
	 * public and static due to the class visibility and loadability
	 * requirements of the remote feedback API.
	 * 
	 * @author sautter
	 */
	public static class BibRefParserFeedbackPanel extends FeedbackPanel {
		private static AnnotationEditorFeedbackPanelRenderer aefpRenderer = new AnnotationEditorFeedbackPanelRenderer();
		
		private AnnotationEditorFeedbackPanel annotationEditor = new AnnotationEditorFeedbackPanel();
		private FeedbackPanelHtmlRendererInstance annotationEditorRenderer;
		
		private JPanel functionPanel = new JPanel(new BorderLayout(), true);
		private JComboBox bibRefType = new JComboBox();
		private JCheckBox noBibRef = new JCheckBox("Not a Bibliographic Reference");
		
		public BibRefParserFeedbackPanel(String title) {
			super(title);
			
			this.bibRefType.setEditable(false);
			
			this.functionPanel.add(this.bibRefType, BorderLayout.WEST);
			this.functionPanel.add(this.noBibRef, BorderLayout.EAST);
			this.add(this.functionPanel, BorderLayout.NORTH);
			
			this.annotationEditor.setFontSize(12);
			this.annotationEditor.setFontName("Verdana");
			this.add(this.annotationEditor, BorderLayout.CENTER);
		}
		
		void setAnnotation(MutableAnnotation annotation) {
			this.annotationEditor.addAnnotation(annotation);
		}
		
		void setBibRefTypes(BibRefType[] types) {
			this.bibRefType.setModel(new DefaultComboBoxModel(types));
		}
		
		void setBibRefType(BibRefType type) {
			for (int t = 0; t < this.bibRefType.getItemCount(); t++)
				if (type.equals(this.bibRefType.getItemAt(t))) {
					this.bibRefType.setSelectedIndex(t);
					break;
				}
		}
		
		void setAllowRemove(boolean ar) {
			if (ar)
				this.noBibRef.setEnabled(true);
			else {
				this.noBibRef.setSelected(false);
				this.noBibRef.setEnabled(false);
			}
		}
		
		BibRefType getBibRefType() {
			return ((BibRefType) this.bibRefType.getSelectedItem());
		}
		
		void addDetailType(String detailType, Color color) {
			this.annotationEditor.addDetailType(detailType, color);
		}
		
		void writeChanges(MutableAnnotation target) {
			AnnotationEditorFeedbackPanel.writeChanges(this.annotationEditor.getTokenStatesAt(0), target);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getComplexity()
		 */
		public int getComplexity() {
			return (this.getDecisionComplexity() + this.getDecisionCount());
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getDecisionComplexity()
		 */
		public int getDecisionComplexity() {
			return this.annotationEditor.getDecisionComplexity();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getDecisionCount()
		 */
		public int getDecisionCount() {
			return this.annotationEditor.getDecisionCount();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeData(java.io.Writer)
		 */
		public void writeData(Writer out) throws IOException {
			BufferedWriter bw = ((out instanceof BufferedWriter) ? ((BufferedWriter) out) : new BufferedWriter(out));
			super.writeData(bw);
			
			//	add exclusion & reference types
			bw.write(this.noBibRef.isEnabled() ? (this.noBibRef.isSelected() ? "E" : "K") : "D");
			bw.newLine();
			bw.write(((BibRefType) this.bibRefType.getSelectedItem()).name);
			bw.newLine();
			for (int c = 0; c < this.bibRefType.getItemCount(); c++) {
				bw.write(((BibRefType) this.bibRefType.getItemAt(c)).toDataString());
				bw.newLine();
			}
			bw.newLine();
			
			//	write content
			this.annotationEditor.writeData(bw);
			
			//	send data
			bw.flush();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#initFields(java.io.Reader)
		 */
		public void initFields(Reader in) throws IOException {
			BufferedReader br = ((in instanceof BufferedReader) ? ((BufferedReader) in) : new BufferedReader(in));
			super.initFields(br);
			
			//	read exclusion & selected bibRefType
			String excludeState = br.readLine();
			if ("D".equals(excludeState)) {
				this.noBibRef.setSelected(false);
				this.noBibRef.setEnabled(false);
			}
			else {
				this.noBibRef.setEnabled(true);
				this.noBibRef.setSelected("E".equals(excludeState));
			}
			String selectedType = br.readLine();
			
			//	read bibRefType list
			String line;
			TreeSet types = new TreeSet();
			while (((line = br.readLine()) != null) && (line.length() != 0)) {
				BibRefType type = BibRefType.parseDataString(line);
				if (type != null)
					types.add(type);
			}
			this.setBibRefTypes((BibRefType[]) types.toArray(new TreeSet[types.size()]));
			this.setBibRefType(new BibRefType(selectedType));
			
			//	read content
			this.annotationEditor.initFields(br);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#getFieldStates()
		 */
		public Properties getFieldStates() {
			Properties fs = this.annotationEditor.getFieldStates();
			if (fs == null)
				return null;
			fs.setProperty(("bibRefType" + 0), ((BibRefType) this.bibRefType.getSelectedItem()).name);
			fs.setProperty(("noBibRef" + 0), (this.noBibRef.isSelected() ? "E" : "K"));
			return fs;
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#setFieldStates(java.util.Properties)
		 */
		public void setFieldStates(Properties states) {
			this.annotationEditor.setFieldStates(states);
			String type = states.getProperty("bibRefType" + 0);
			if (type != null)
				this.setBibRefType(new BibRefType(type));
			this.noBibRef.setSelected("E".equals(states.getProperty(("noBibRef" + 0), "K")));
		}
		
		private final FeedbackPanelHtmlRendererInstance getRendererInstance() {
			if (this.annotationEditorRenderer == null)
				this.annotationEditorRenderer = aefpRenderer.getRendererInstance(this.annotationEditor);
			return this.annotationEditorRenderer;
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeJavaScriptInitFunctionBody(java.io.Writer)
		 */
		public void writeJavaScriptInitFunctionBody(Writer out) throws IOException {
			this.getRendererInstance().writeJavaScriptInitFunctionBody(out);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeJavaScript(java.io.Writer)
		 */
		public void writeJavaScript(Writer out) throws IOException {
			this.getRendererInstance().writeJavaScript(out);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writeCssStyles(java.io.Writer)
		 */
		public void writeCssStyles(Writer out) throws IOException {
			this.getRendererInstance().writeCssStyles(out);
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#writePanelBody(java.io.Writer)
		 */
		public void writePanelBody(Writer out) throws IOException {
			BufferedLineWriter bw = ((out instanceof BufferedLineWriter) ? ((BufferedLineWriter) out) : new BufferedLineWriter(out));
			
			bw.writeLine("<table class=\"part\" id=\"part" + 0 + "\">");
			bw.writeLine("<tr>");
			
			bw.writeLine("<td>");
			bw.writeLine("Reference Type:");
			bw.writeLine("<select name=\"bibRefType" + 0 + "\">");
			for (int c = 0; c < this.bibRefType.getItemCount(); c++) {
				BibRefType type = ((BibRefType)  this.bibRefType.getItemAt(c));
				bw.writeLine("<option value=\"" + type.name + "\"" + ((c == this.bibRefType.getSelectedIndex()) ? " selected" : "") + ">" + type.label + "</option>");
			}
			bw.writeLine("</select>");
			bw.writeLine("</td>");
			
			bw.writeLine("<td>");
			bw.writeLine("</td>");
			
			bw.writeLine("<td>");
			if (this.noBibRef.isEnabled()) {
				bw.writeLine("Not a Bibliographic Reference");
				bw.writeLine("<input name=\"noBibRef" + 0 + "\" type=\"checkbox\" value=\"E\"" + (this.noBibRef.isSelected() ? " checked" : "") + ">");
			}
			bw.writeLine("</td>");
			
			bw.writeLine("</tr>");
			bw.writeLine("</table>");
			
			this.getRendererInstance().writePanelBody(bw);
			
			if (bw != out)
				bw.flush();
		}
		
		/* (non-Javadoc)
		 * @see de.uka.ipd.idaho.gamta.util.feedback.FeedbackPanel#readResponse(java.util.Properties)
		 */
		public void readResponse(Properties response) {
			this.getRendererInstance().readResponse(response);
			String type = response.getProperty("bibRefType" + 0);
			if (type != null)
				this.setBibRefType(new BibRefType(type));
			this.noBibRef.setSelected("E".equals(response.getProperty(("noBibRef" + 0), "K")));
		}
	}
	
	/**
	 * 
	 * @param adp
	 * @return
	 */
	public static RefParse getInstance(AnalyzerDataProvider adp) {
		RefParse rp = ((RefParse) instances.get(adp.getAbsolutePath()));
		if (rp == null) {
			rp = new RefParse() {};
			rp.setDataProvider(adp);
			instances.put(adp.getAbsolutePath(), rp);
		}
		return rp;
	}
	private static HashMap instances = new HashMap(3);
}