EvilTwin — Juice WRLD (JW) Feature Extraction Notes
===================================================

Source reviewed: EvilTwin(3).py
Output script: EvilTwin_no_JW.py

WHAT WAS REMOVED FROM THE BOT
------------------------------

1) Prefix commands

• ~jwgb [song name]
  Group-buy archive lookup. With no argument, it fetched the newest group-buy entry; with a name, it searched entries by title/details. The source included matching/scoring, date formatting, and a formatted embed. It also had a retry/cooldown and a saved archive snapshot fallback when the live API could not be reached.

• ~jwlyric <song>
  Looked up a catalog song and displayed lyrics when the API response contained lyrics.

• ~jwlyricsearch <phrase>
  Searched the catalog for songs whose lyrics matched a phrase.

• ~jwcover <song or album>
  Searched community/catalog entries for matching cover art, downloaded candidate images with a size limit, checked that responses were images, and sent the image(s) or direct links in an embed.

• ~jwfiles <song>
  Searched the API's file listing for audio files associated with a song and displayed matching file information/links.

• ~jwradio [off]
  Started a continuous random Juice WRLD radio session using the API's compressed-audio stream endpoint. It reused the bot's music queue/player, fetched another track after each track ended, avoided repeating the immediately previous title when possible, retried temporary catalog/stream failures, and could be turned off with `~jwradio off`. While active it restricted normal music commands so radio could own the shared player.

• ~jwplay [song] (alias: ~jwp)
  Played a selected Juice WRLD catalog track, or selected a random track when no song was supplied. It used the compressed audio endpoint directly with FFmpeg instead of downloading the original audio file as a fallback, then put the track into the shared music queue.

• ~jwsong <search> (aliases: ~jwsearch, ~jwmusicsearch)
  Searched the Juice WRLD catalog and showed detailed song metadata. The interactive result view allowed selecting alternate/related matches and could link into the API file browser for matching audio.

2) Automatic Juice WRLD tracker feed
  The bot also had a background tracker task separate from prefix commands. When JUICEWRLD_CHANNEL_ID was configured, it polled the API at a configurable interval, saved seen event IDs to avoid reposting duplicates after restarts, established a baseline, and posted embeds for new/changed catalog entries. It distinguished catalog creation events from other changes and included available metadata/artwork and change details.

3) Shared Juice WRLD support code removed
  - API request helpers and configuration for API base/key/channel.
  - Group-buy API parsing, matching, date formatting, and embed construction.
  - Song search/detail/catalog helpers and lyric extraction.
  - Artwork URL cleaning, image downloading, validation, and file-size limits.
  - Audio catalog parsing, audio candidate scoring/filtering, compressed endpoint URL construction, and radio catalog cache helpers.
  - Tracker persistence, deduplication, polling task, and tracker embeds.
  - Juice-specific state variables and radio control flow in the generic music engine.
  - Juice WRLD-specific page from `~commands`/help and the Juice WRLD tile from the Vault Control Center.

WHAT REMAINS IN EvilTwin_no_JW.py
---------------------------------

• The general music player remains, including `~play`, queue/skip/stop, pause/resume, volume, loop, now-playing, and leave/disconnect controls.
• Other bot features outside the Juice WRLD integration were preserved in the edited copy: member profiles/history, moderation, server member-stat channels, AI chat, FreeStuff alerts, patch notes, Twitch Drops, automatic replies, traffic monitor, and Vault Control Center.
• The help pages were adjusted to remove the Juice WRLD page and references to JW commands/tracker.
• The ordinary music player no longer checks or reserves a shared queue for Juice WRLD Radio.
• The requirements file does not need changes for this removal; its listed packages are still used by other bot features.

HOST SETTINGS NO LONGER USED BY THIS FEATURE
--------------------------------------------

These Juice WRLD-specific environment settings were removed from the script:
• JUICEWRLD_API_BASE
• JUICEWRLD_API_KEY
• JUICEWRLD_CHANNEL_ID
• JUICEWRLD_POLL_MINUTES
• JUICEWRLD_STATE_FILE
• JUICEWRLD_CATALOG_CACHE_FILE
• VAULTBOT_JW_PLAYBACK_BITRATE

You can remove those settings from the hosting panel if you no longer use them for anything else. Keep DISCORD_TOKEN and all settings for the remaining features.

VALIDATION
----------

• Python syntax compilation passed for EvilTwin_no_JW.py.
• This was a static code edit; I did not connect to Discord or run a live bot test.
• The original uploaded file was left unchanged. Deploy the new file only after keeping a backup of your current working script and verifying your host's expected entry filename.
